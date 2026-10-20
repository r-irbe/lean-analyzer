/**
 * js/lean_analyzer_bridge.js
 * In-process WebAssembly & ES module abstract evaluation bridge for Lean 4 terms.
 */

export const AbstractSign = Object.freeze({
  Bottom: 0,
  Zero: 1,
  Positive: 2,
  NonNegative: 3,
  Negative: 4,
  NonPositive: 5,
  NonZero: 6,
  Top: 7
});

export const AbstractBool = Object.freeze({
  Bottom: 0,
  False: 1,
  True: 2,
  Top: 3
});

export const DiagnosticKind = Object.freeze({
  NatSubTruncation: "NatSubTruncation",
  NatDivModByZero: "NatDivModByZero",
  DeadBranch: "DeadBranch"
});

export class LeanAnalyzerBridge {
  constructor(wasmInstance = null) {
    this.wasm = wasmInstance;
    this.memory = wasmInstance ? wasmInstance.exports.memory : null;
  }

  getVersion() {
    if (this.wasm && this.wasm.exports.lean_analyzer_version) {
      return this.wasm.exports.lean_analyzer_version();
    }
    return 100;
  }

  joinSigns(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_join_signs) {
      return this.wasm.exports.lean_analyzer_join_signs(a, b);
    }
    return (a | b) & 7;
  }

  meetSigns(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_meet_signs) {
      return this.wasm.exports.lean_analyzer_meet_signs(a, b);
    }
    return (a & b) & 7;
  }

  _callWasmIntervalOp(fnName, min1, max1, min2, max2) {
    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports[fnName] === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = this.wasm.exports[fnName](
        BigInt(Math.trunc(min1)),
        BigInt(Math.trunc(max1)),
        BigInt(Math.trunc(min2)),
        BigInt(Math.trunc(max2)),
        ptr
      );
      if (ok === 1) {
        const view = new BigInt64Array(this.memory.buffer, ptr, 2);
        return { min: Number(view[0]), max: Number(view[1]) };
      }
    }
    return null;
  }

  evalNatAdd(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_add", min1, max1, min2, max2);
    if (w) return w;
    return {
      min: Math.max(0, min1 + min2),
      max: Math.max(0, max1 + max2)
    };
  }

  evalNatSub(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_sub", min1, max1, min2, max2);
    if (w) return w;
    return {
      min: Math.max(0, min1 - max2),
      max: Math.max(0, max1 - min2)
    };
  }

  evalNatMul(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_mul", min1, max1, min2, max2);
    if (w) return w;
    const p1 = min1 * min2;
    const p2 = min1 * max2;
    const p3 = max1 * min2;
    const p4 = max1 * max2;
    return {
      min: Math.max(0, Math.min(p1, p2, p3, p4)),
      max: Math.max(0, Math.max(p1, p2, p3, p4))
    };
  }

  evalBoolNot(val) {
    if (this.wasm && this.wasm.exports.lean_analyzer_bool_not) {
      return this.wasm.exports.lean_analyzer_bool_not(val);
    }
    switch (val) {
      case AbstractBool.False: return AbstractBool.True;
      case AbstractBool.True: return AbstractBool.False;
      case AbstractBool.Bottom: return AbstractBool.Bottom;
      default: return AbstractBool.Top;
    }
  }

  evalBoolAnd(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_bool_and) {
      return this.wasm.exports.lean_analyzer_bool_and(a, b);
    }
    if (a === AbstractBool.False || b === AbstractBool.False) {
      return AbstractBool.False;
    }
    if (a === AbstractBool.True && b === AbstractBool.True) {
      return AbstractBool.True;
    }
    if (a === AbstractBool.Bottom || b === AbstractBool.Bottom) {
      return AbstractBool.Bottom;
    }
    return AbstractBool.Top;
  }

  evalBoolOr(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_bool_or) {
      return this.wasm.exports.lean_analyzer_bool_or(a, b);
    }
    if (a === AbstractBool.True || b === AbstractBool.True) {
      return AbstractBool.True;
    }
    if (a === AbstractBool.False && b === AbstractBool.False) {
      return AbstractBool.False;
    }
    if (a === AbstractBool.Bottom || b === AbstractBool.Bottom) {
      return AbstractBool.Bottom;
    }
    return AbstractBool.Top;
  }

  evalBoolXor(a, b) {
    if (a === AbstractBool.Bottom || b === AbstractBool.Bottom) {
      return AbstractBool.Bottom;
    }
    if ((a === AbstractBool.True && b === AbstractBool.True) || (a === AbstractBool.False && b === AbstractBool.False)) {
      return AbstractBool.False;
    }
    if ((a === AbstractBool.True && b === AbstractBool.False) || (a === AbstractBool.False && b === AbstractBool.True)) {
      return AbstractBool.True;
    }
    return AbstractBool.Top;
  }

  evalNatPow(min1, max1, min2, max2) {
    if (max2 === 0) {
      return { min: 1, max: 1 };
    }
    return {
      min: Math.max(0, Math.pow(Math.max(0, min1), Math.max(0, min2))),
      max: Math.max(0, Math.pow(Math.max(0, max1), Math.max(0, max2)))
    };
  }

  evalNatMin(min1, max1, min2, max2) {
    return {
      min: Math.min(min1, min2),
      max: Math.min(max1, max2)
    };
  }

  evalNatMax(min1, max1, min2, max2) {
    return {
      min: Math.max(min1, min2),
      max: Math.max(max1, max2)
    };
  }

  /**
   * Lean 4 Nat division interval transfer (`a / 0 = 0`).
   */
  evalNatDiv(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_div", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (bHi === 0) {
      return { min: 0, max: 0 };
    }
    if (bLo > 0) {
      return {
        min: Math.trunc(aLo / bHi),
        max: Math.trunc(aHi / bLo)
      };
    }
    // bLo === 0 && bHi > 0: divisor may be 0 (giving 0) or in [1, bHi].
    return {
      min: 0,
      max: aHi
    };
  }

  /**
   * Lean 4 Nat modulo interval transfer (`a % 0 = a`), including single-quotient-bucket exactness.
   */
  evalNatMod(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_mod", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (bHi === 0) {
      return { min: aLo, max: aHi };
    }
    if (bLo === bHi && bLo > 0) {
      const k = bLo;
      if (Math.trunc(aLo / k) === Math.trunc(aHi / k)) {
        return { min: aLo % k, max: aHi % k };
      }
      return { min: 0, max: Math.min(aHi, k - 1) };
    }
    if (bLo > 0) {
      if (aHi < bLo) {
        return { min: aLo, max: aHi };
      }
      return { min: 0, max: Math.min(aHi, bHi - 1) };
    }
    // Divisor includes 0 (`a % 0 = a`) and positive values up to `bHi`:
    return { min: 0, max: aHi };
  }

  /**
   * Bitwise AND interval transfer (Warren Ch. 4 bounds).
   */
  evalNatLand(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_land", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (aLo === aHi && bLo === bHi) {
      const v = Number(BigInt(aLo) & BigInt(bLo));
      return { min: v, max: v };
    }
    return { min: 0, max: Math.min(aHi, bHi) };
  }

  /**
   * Bitwise OR interval transfer (Warren Ch. 4 bounds via next power of two minus 1).
   */
  evalNatLor(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_lor", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (aLo === aHi && bLo === bHi) {
      const v = Number(BigInt(aLo) | BigInt(bLo));
      return { min: v, max: v };
    }
    const lo = Math.max(aLo, bLo);
    const maxIn = Math.max(aHi, bHi);
    if (maxIn === 0) {
      return { min: 0, max: 0 };
    }
    let mask = 1n;
    const bigMax = BigInt(maxIn);
    while (mask <= bigMax) {
      mask <<= 1n;
    }
    return { min: lo, max: Number(mask - 1n) };
  }

  /**
   * Bitwise XOR interval transfer (Warren Ch. 4 bounds).
   */
  evalNatXor(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_xor", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (aLo === aHi && bLo === bHi) {
      const v = Number(BigInt(aLo) ^ BigInt(bLo));
      return { min: v, max: v };
    }
    const maxIn = Math.max(aHi, bHi);
    if (maxIn === 0) {
      return { min: 0, max: 0 };
    }
    let mask = 1n;
    const bigMax = BigInt(maxIn);
    while (mask <= bigMax) {
      mask <<= 1n;
    }
    return { min: 0, max: Number(mask - 1n) };
  }

  /**
   * Bitwise shift-left interval transfer `a <<< b`.
   */
  evalNatShl(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_shl", min1, max1, min2, max2);
    if (w) return w;
    const aLo = BigInt(Math.max(0, Math.trunc(min1)));
    const aHi = BigInt(Math.max(Number(aLo), Math.trunc(max1)));
    const bLo = BigInt(Math.max(0, Math.trunc(min2)));
    const bHi = BigInt(Math.max(Number(bLo), Math.trunc(max2)));
    return {
      min: Number(aLo << bLo),
      max: Number(aHi << bHi)
    };
  }

  /**
   * Bitwise shift-right interval transfer `a >>> b`.
   */
  evalNatShr(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_shr", min1, max1, min2, max2);
    if (w) return w;
    const aLo = BigInt(Math.max(0, Math.trunc(min1)));
    const aHi = BigInt(Math.max(Number(aLo), Math.trunc(max1)));
    const bLo = BigInt(Math.max(0, Math.trunc(min2)));
    const bHi = BigInt(Math.max(Number(bLo), Math.trunc(max2)));
    return {
      min: Number(aLo >> bHi),
      max: Number(aHi >> bLo)
    };
  }

  /**
   * Mutual Granger reduction of interval `[min, max]` against congruence `offset (mod stride)`.
   * Returns `{ min, max, stride, offset }` or `null` if the intersection is empty (Bottom).
   */
  reduceIntervalCongruence(min, max, stride, offset) {
    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_reduce_interval_congruence === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = this.wasm.exports.lean_analyzer_reduce_interval_congruence(
        BigInt(Math.trunc(min)),
        BigInt(Math.trunc(max)),
        BigInt(Math.max(0, Math.trunc(stride))),
        BigInt(Math.max(0, Math.trunc(offset))),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.memory.buffer, ptr, 4);
      return {
        min: Number(view[0]),
        max: Number(view[1]),
        stride: Number(view[2]),
        offset: Number(view[3])
      };
    }
    const lo = Math.max(0, Math.trunc(min));
    const hi = Math.trunc(max);
    if (lo > hi) {
      return null;
    }
    const s = Math.max(0, Math.trunc(stride));
    const o = s === 0 ? Math.max(0, Math.trunc(offset)) : ((Math.trunc(offset) % s) + s) % s;
    if (s === 0) {
      if (o >= lo && o <= hi) {
        return { min: o, max: o, stride: 0, offset: o };
      }
      return null;
    }
    const remLo = lo % s;
    const deltaLo = remLo <= o ? (o - remLo) : (s - (remLo - o));
    const tightMin = lo + deltaLo;
    if (tightMin > hi) {
      return null;
    }
    const remHi = hi % s;
    const deltaHi = remHi >= o ? (remHi - o) : (s - (o - remHi));
    const tightMax = hi - deltaHi;
    if (tightMin > tightMax) {
      return null;
    }
    if (tightMin === tightMax) {
      return { min: tightMin, max: tightMax, stride: 0, offset: tightMin };
    }
    return { min: tightMin, max: tightMax, stride: s, offset: o };
  }

  /**
   * Discharges Lean 4 termination obligation `n - (i + step) < n - i` under guard `i - n <= guardDiff`.
   * Returns `AbstractBool` (`Bottom=0, False=1, True=2, Top=3`).
   */
  checkZoneSubDecreasing(guardDiff, step) {
    if (this.wasm && this.wasm.exports.lean_analyzer_zone_check_sub_decreasing) {
      return this.wasm.exports.lean_analyzer_zone_check_sub_decreasing(
        BigInt(Math.trunc(guardDiff)),
        BigInt(Math.trunc(step))
      );
    }
    if (step <= 0) {
      return AbstractBool.False;
    }
    if (guardDiff <= -1) {
      return AbstractBool.True;
    }
    return AbstractBool.Top;
  }

  /**
   * Emits actionable static diagnostic certificates for a binary Nat operation on `[min1, max1]` and `[min2, max2]`.
   */
  diagnoseNatOp(op, min1, max1, min2, max2) {
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    const certs = [];
    if (op === "Nat.sub" || op === "HSub.hSub" || op === "-") {
      if (aHi <= bLo && bLo > 0) {
        certs.push({
          kind: DiagnosticKind.NatSubTruncation,
          operator: op,
          summary: `Natural subtraction \`${op}\` on [${aLo}, ${aHi}] - [${bLo}, ${bHi}] saturates to [0, 0].`,
          hint: "Add guard `b <= a` or switch to `Int` subtraction if negative values are intended."
        });
      }
    } else if (
      op === "Nat.div" ||
      op === "HDiv.hDiv" ||
      op === "/" ||
      op === "Nat.mod" ||
      op === "HMod.hMod" ||
      op === "%"
    ) {
      if (bLo <= 0 && 0 <= bHi) {
        certs.push({
          kind: DiagnosticKind.NatDivModByZero,
          operator: op,
          summary: `Divisor interval [${bLo}, ${bHi}] in \`${op}\` includes 0 (Lean total semantics: a / 0 = 0, a % 0 = a).`,
          hint: "Prove `0 < divisor` or guard against zero divisor."
        });
      }
    }
    return certs;
  }

  /**
   * Tightens two natural-number intervals `[min0, max0]` and `[min1, max1]`
   * under relational octagon constraints `sumLo <= x0 + x1 <= sumHi` and `x0 - x1 <= diffHi`.
   * Returns `[{ min, max }, { min, max }]` or `null` if unsatisfiable (`Bottom`).
   */
  reduceOctagonTwoVars(min0, max0, min1, max1, sumLo, sumHi, diffHi = Number.POSITIVE_INFINITY) {
    const MAX_I64 = 9223372036854775807n;
    const toI64 = (v) => (!Number.isFinite(v) ? MAX_I64 : BigInt(Math.trunc(v)));

    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_octagon_reduce_two_vars === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = this.wasm.exports.lean_analyzer_octagon_reduce_two_vars(
        toI64(Math.max(0, min0)),
        toI64(max0),
        toI64(Math.max(0, min1)),
        toI64(max1),
        toI64(Math.max(0, sumLo)),
        toI64(sumHi),
        toI64(diffHi),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.memory.buffer, ptr, 4);
      const fromI64 = (b) => (b >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(b));
      return [
        { min: fromI64(view[0]), max: fromI64(view[1]) },
        { min: fromI64(view[2]), max: fromI64(view[3]) }
      ];
    }

    let lo0 = Math.max(0, Math.trunc(min0));
    let hi0 = Number.isFinite(max0) ? Math.trunc(max0) : Number.POSITIVE_INFINITY;
    let lo1 = Math.max(0, Math.trunc(min1));
    let hi1 = Number.isFinite(max1) ? Math.trunc(max1) : Number.POSITIVE_INFINITY;
    const sLo = Math.max(0, Math.trunc(sumLo));
    const sHi = Number.isFinite(sumHi) ? Math.trunc(sumHi) : Number.POSITIVE_INFINITY;
    const dHi = Number.isFinite(diffHi) ? Math.trunc(diffHi) : Number.POSITIVE_INFINITY;

    for (let iter = 0; iter < 4; iter++) {
      if (Number.isFinite(hi1)) lo0 = Math.max(lo0, sLo - hi1);
      if (Number.isFinite(sHi)) hi0 = Math.min(hi0, sHi - lo1);
      if (Number.isFinite(hi0)) lo1 = Math.max(lo1, sLo - hi0);
      if (Number.isFinite(sHi)) hi1 = Math.min(hi1, sHi - lo0);

      if (Number.isFinite(dHi)) {
        if (Number.isFinite(hi1)) hi0 = Math.min(hi0, hi1 + dHi);
        lo1 = Math.max(lo1, lo0 - dHi);
        if (Number.isFinite(sHi)) {
          hi0 = Math.min(hi0, Math.floor((sHi + dHi) / 2));
        }
      }
      if (lo0 > hi0 || lo1 > hi1) return null;
    }

    if (lo0 + lo1 > sHi || hi0 + hi1 < sLo) return null;
    if (Number.isFinite(dHi) && lo0 - hi1 > dHi) return null;

    return [
      { min: lo0, max: hi0 },
      { min: lo1, max: hi1 }
    ];
  }
}

export async function loadLeanAnalyzerBridge(wasmUrlOrBuffer = null) {
  if (!wasmUrlOrBuffer) {
    try {
      const fs = await import("node:fs/promises");
      const url = new URL("../data/lean_analyzer.wasm", import.meta.url);
      wasmUrlOrBuffer = await fs.readFile(url);
    } catch {
      return new LeanAnalyzerBridge(null);
    }
  }
  const bytes = wasmUrlOrBuffer instanceof Uint8Array || wasmUrlOrBuffer instanceof ArrayBuffer
    ? wasmUrlOrBuffer
    : await (await fetch(wasmUrlOrBuffer)).arrayBuffer();
  const { instance } = await WebAssembly.instantiate(bytes, {});
  return new LeanAnalyzerBridge(instance);
}
