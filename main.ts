// Tiny stack VM: faithful implementation of make.fun's tiny stack ISA v1
// (kit ISA.md; reference generator/subject/vm.mjs). Every trap code, limit
// and wrapping rule matches the reference, including the ones the house
// baseline (plain-vm 1.0.0) gets wrong: Math.imul MUL, unsigned DIVU/MODU/
// LTU, shifts masked to 5 bits, PUSH8 sign extension, EXIT low byte, trap
// codes 2-11, step (1,000,000) and output (65,536) limits. One tight loop,
// Int32Array stacks, preallocated output, PRINT digits written by hand.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables: [opcode, immediate bytes, pops, pushes].
const IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256), OK = new Uint8Array(256);
for (const s of [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]]) {
  OK[s[0]] = 1; IM[s[0]] = s[1]; PO[s[0]] = s[2]; PU[s[0]] = s[3];
}

// Returns [output buffer, output length, exit code].
function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  for (;;) {
    if (steps === 1000000) return [out, ol, 10];
    if (pc < 0 || pc >= n) return [out, ol, 9];
    const op = p[pc];
    if (!OK[op]) return [out, ol, 5];
    const imm = IM[op];
    if (pc + imm >= n) return [out, ol, 9];
    steps++;
    if (sp < PO[op]) return [out, ol, 2];
    if (sp - PO[op] + PU[op] > 256) return [out, ol, 3];
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0: return [out, ol, 0];
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (!b) return [out, ol, 4]; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (!b) return [out, ol, 4]; r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (!b) return [out, ol, 4]; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (!b) return [out, ol, 4]; r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; D[sp++] = r; break;
      }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (csp === 64) return [out, ol, 7];
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (csp === 0) return [out, ol, 8];
        pc = C[--csp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return [out, ol, 6];
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return [out, ol, 6];
        sp -= 2; M[a] = v;
        break;
      }
      case 80: {
        const v = D[sp - 1];
        let u = v < 0 ? -v : v;
        let len = v < 0 ? 1 : 0;
        if (u < 10) len += 1;
        else if (u < 100) len += 2;
        else if (u < 1000) len += 3;
        else if (u < 10000) len += 4;
        else if (u < 100000) len += 5;
        else if (u < 1000000) len += 6;
        else if (u < 10000000) len += 7;
        else if (u < 100000000) len += 8;
        else if (u < 1000000000) len += 9;
        else len += 10;
        if (ol + len > 65536) return [out, ol, 11];
        sp--;
        let i = ol + len;
        if (u === 0) out[--i] = 48;
        else while (u > 0) { out[--i] = 48 + (u % 10); u = (u / 10) | 0; }
        if (v < 0) out[--i] = 45;
        ol += len;
        break;
      }
      case 81:
        if (ol + 1 > 65536) return [out, ol, 11];
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return [out, ol, D[--sp] & 255];
      default: return [out, ol, 5];
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r[0].subarray(0, r[1]));
  writeFileSync(join(O, id, 'exit.txt'), r[2] + '\n');
}
