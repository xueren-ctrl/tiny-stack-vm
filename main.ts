// A tiny stack VM for make.fun's ISA (version 1): 32-bit wrapping integers, a 256-value data stack, a 64-entry
// call stack, 256 words of memory, input/output, ten traps with their own exit codes, and a step and an output
// limit. Every rule follows generator/subject/ISA.md and its reference VM, vm.mjs: the check order per step
// (step limit, pc range, unknown opcode, cut-off immediate, stack underflow, stack overflow, then the
// instruction's own traps), and the exact arithmetic of each opcode.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: [byte, immediate bytes, pops, pushes]. IM stores immediate+1 so 0 means "no such opcode".
const IM = new Uint8Array(256);
const PO = new Uint8Array(256);
const PU = new Uint8Array(256);
for (const e of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2], [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1], [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1],
  [32, 0, 2, 1], [33, 0, 2, 1], [34, 0, 2, 1],
  [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0],
  [64, 0, 1, 1], [65, 0, 2, 0],
  [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
]) {
  IM[e[0]] = e[1] + 1;
  PO[e[0]] = e[2];
  PU[e[0]] = e[3];
}

/** Runs one program on its input: [the bytes it wrote, its exit code]. A trap's exit code is the trap's code. */
function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let st = 0;
  for (;;) {
    if (st === 1000000) return [out.subarray(0, ol), 10];
    if (pc < 0 || pc >= n) return [out.subarray(0, ol), 9];
    const op = p[pc];
    const im = IM[op];
    if (!im) return [out.subarray(0, ol), 5];
    const imm = im - 1;
    if (pc + imm >= n) return [out.subarray(0, ol), 9];
    st++;
    const nx = pc + 1 + imm;
    const po = PO[op];
    const pu = PU[op];
    if (sp < po) return [out.subarray(0, ol), 2];
    if (sp - po + pu > 256) return [out.subarray(0, ol), 3];
    pc = nx;
    switch (op) {
      case 0:
        return [out.subarray(0, ol), 0];
      case 1:
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 2:
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 3:
        sp--;
        break;
      case 4:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 23:
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19:
            if (b === 0) return [out.subarray(0, ol), 4];
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 20:
            if (b === 0) return [out.subarray(0, ol), 4];
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21:
            if (b === 0) return [out.subarray(0, ol), 4];
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22:
            if (b === 0) return [out.subarray(0, ol), 4];
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // 34: LTU
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let t = true;
        if (op !== 48) {
          const v = D[--sp];
          t = op === 49 ? v === 0 : v !== 0;
        }
        if (t) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return [out.subarray(0, ol), 7];
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return [out.subarray(0, ol), 8];
        pc = C[--cp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return [out.subarray(0, ol), 6];
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1];
        const v = D[sp - 2];
        if (a < 0 || a >= 256) return [out.subarray(0, ol), 6];
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return [out.subarray(0, ol), 11];
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (ol + 1 > 65536) return [out.subarray(0, ol), 11];
        out[ol++] = D[--sp] & 255;
        break;
      case 82:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83:
        return [out.subarray(0, ol), D[--sp] & 255];
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r[0]);
  writeFileSync(join(O, id, 'exit.txt'), r[1] + '\n');
}
