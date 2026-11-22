import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const T = new Int16Array(256).fill(-1);
function d(im: number, po: number, pu: number, list: number[]) {
  for (const b of list) T[b] = im | (po << 3) | (pu << 5);
}
d(1, 0, 1, [0x01]);
d(4, 0, 1, [0x02]);
d(0, 1, 0, [0x03, 0x50, 0x51, 0x53]);
d(0, 1, 2, [0x04]);
d(0, 2, 2, [0x05]);
d(0, 2, 3, [0x06]);
d(0, 3, 3, [0x07]);
d(0, 2, 1, [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]);
d(0, 1, 1, [0x17, 0x1b, 0x40]);
d(2, 0, 0, [0x30, 0x33]);
d(2, 1, 0, [0x31, 0x32]);
d(0, 2, 0, [0x41]);
d(0, 0, 1, [0x52]);
d(0, 0, 0, [0x00, 0x34]);

function run(p: Uint8Array, inp: Uint8Array) {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const bad = (c: number) => ({ out: out.subarray(0, olen), exit: c });
  for (;;) {
    if (steps === 1000000) return bad(10);
    if (pc < 0 || pc >= n) return bad(9);
    const op = p[pc];
    const v = T[op];
    if (v < 0) return bad(5);
    const im = v & 7, po = (v >> 3) & 3, pu = (v >> 5) & 3;
    if (pc + im >= n) return bad(9);
    steps++;
    const nx = pc + 1 + im;
    if (sp < po) return bad(2);
    if (sp - po + pu > 256) return bad(3);
    pc = nx;
    switch (op) {
      case 0x00: return { out: out.subarray(0, olen), exit: 0 };
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return bad(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: if (b === 0) return bad(4); r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: if (b === 0) return bad(4); r = ((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return bad(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const t = D[--sp];
          take = op === 0x31 ? t === 0 : t !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: if (csp === 64) return bad(7); C[csp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34: if (csp === 0) return bad(8); pc = C[--csp]; break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return bad(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], val = D[sp - 2];
        if (addr < 0 || addr > 255) return bad(6);
        sp -= 2;
        M[addr] = val;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return bad(11);
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return bad(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      default: return { out: out.subarray(0, olen), exit: D[--sp] & 255 };
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.exit}\n`);
}