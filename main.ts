// Tiny stack VM for make.fun's tiny-stack ISA (kit ISA.md).
// One run answers every instance in MAKEFUN_INPUT_DIR, writing
// stdout.bin + exit.txt per instance under MAKEFUN_OUTPUT_DIR.
// Traps throw their exit code; HALT/EXIT break out with code set.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// Stack pops per opcode. Unknown opcodes and immediate-only opcodes
// (JZ/JNZ/CALL, whose immediate check precedes the stack check) are 0.
const NP = new Uint8Array(84);
for (let i = 16; i < 35; i++) NP[i] = 2;
NP[23] = 1; NP[27] = 1; NP[31] = 0;
NP[3] = 1; NP[4] = 1; NP[5] = 2; NP[6] = 2; NP[7] = 3;
NP[64] = 1; NP[65] = 2; NP[80] = 1; NP[81] = 1; NP[83] = 1;

// Run one program; returns [exit code, output bytes].
function run(p, inp) {
  const st = new Int32Array(256); // data stack
  const cs = new Int32Array(64); // call stack of return addresses
  const mem = new Int32Array(256); // memory words
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, steps = 0, ip = 0, ol = 0;
  const n = p.length;
  let code = 0;
  try {
  outer: for (;;) {
    if (steps === 1e6) throw 10; // step limit first
    if (pc < 0 || pc >= n) throw 9; // pc out of range
    steps++;
    const op = p[pc];
    if (sp < NP[op]) throw 2; // stack underflow, before the op's own traps
    switch (op) {
      case 0: break outer; // HALT: exit 0
      case 1: // PUSH8: byte sign-extended
        if (pc + 1 >= n) throw 9;
        if (sp > 255) throw 3;
        st[sp++] = p[pc + 1] < 128 ? p[pc + 1] : p[pc + 1] - 256;
        pc += 2; break;
      case 2: // PUSH32: little-endian signed 32-bit
        if (pc + 4 >= n) throw 9;
        if (sp > 255) throw 3;
        st[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5; break;
      case 3: sp--; pc++; break; // POP
      case 4: // DUP
        if (sp > 255) throw 3;
        st[sp] = st[sp - 1]; sp++; pc++; break;
      case 5: // SWAP
        { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }
        pc++; break;
      case 6: // OVER
        if (sp > 255) throw 3;
        st[sp] = st[sp - 2]; sp++; pc++; break;
      case 7: // ROT: (a b c -- b c a)
        { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; }
        pc++; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: { // binary ops: pop 2, push 1
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (b === 0) throw 4; r = (a / b) | 0; }
        else if (op === 20) { if (b === 0) throw 4; r = a % b; }
        else if (op === 21) { if (b === 0) throw 4; r = ((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (b === 0) throw 4; r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        st[sp - 2] = r; sp--; pc++; break;
      }
      case 23: st[sp - 1] = (-st[sp - 1]) | 0; pc++; break; // NEG wraps
      case 27: st[sp - 1] = ~st[sp - 1]; pc++; break; // NOT
      case 48: { // JMP: pc = next instruction + signed offset
        if (pc + 2 >= n) throw 9;
        let off = p[pc + 1] | (p[pc + 2] << 8);
        if (off >= 32768) off -= 65536;
        pc = pc + 3 + off; break;
      }
      case 49: { // JZ
        if (pc + 2 >= n) throw 9;
        if (sp < 1) throw 2;
        const v = st[--sp];
        let off = p[pc + 1] | (p[pc + 2] << 8);
        if (off >= 32768) off -= 65536;
        pc = v === 0 ? pc + 3 + off : pc + 3; break;
      }
      case 50: { // JNZ
        if (pc + 2 >= n) throw 9;
        if (sp < 1) throw 2;
        const v = st[--sp];
        let off = p[pc + 1] | (p[pc + 2] << 8);
        if (off >= 32768) off -= 65536;
        pc = v !== 0 ? pc + 3 + off : pc + 3; break;
      }
      case 51: // CALL: push return address, jump to unsigned target
        if (pc + 2 >= n) throw 9;
        if (cp > 63) throw 7;
        cs[cp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8); break;
      case 52: // RET
        if (cp === 0) throw 8;
        pc = cs[--cp]; break;
      case 64: // LOAD
        { const a = st[sp - 1];
          if (a < 0 || a > 255) throw 6;
          st[sp - 1] = mem[a]; }
        pc++; break;
      case 65: // STORE: (v addr --)
        { const a = st[--sp], v = st[--sp];
          if (a < 0 || a > 255) throw 6;
          mem[a] = v; }
        pc++; break;
      case 80: { // PRINT: decimal ASCII, no newline
        const s = String(st[--sp]);
        if (ol + s.length > 65536) throw 11; // writes none of its bytes
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        pc++; break;
      }
      case 81: // PUTC: one byte, v & 255
        if (ol + 1 > 65536) throw 11;
        out[ol++] = st[--sp] & 255; pc++; break;
      case 82: // IN: next input byte, -1 once exhausted
        if (sp > 255) throw 3;
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        pc++; break;
      case 83: // EXIT: code is the low byte
        code = st[--sp] & 255;
        break outer;
      default: throw 5; // unknown opcode
    }
  }
  } catch (e) { if (typeof e === 'number') code = e; else throw e; }
  return [code, out.subarray(0, ol)];
}

for (const id of readdirSync(I).sort()) {
  const [code, bytes] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), bytes);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
