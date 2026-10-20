# lean-analyzer

Ultra-fast, in-process abstract interpreter, relational domain solver, and zero-copy `.ilean` indexer for Lean 4, compiled to WebAssembly and native Rust.

For detailed usage, API reference, and examples across Rust, JavaScript/TypeScript, and Lean 4, see [USER_GUIDE.md](USER_GUIDE.md).

## Key Features

- **Zero-Dependency WASM Binary (~49 KB)**: Compiles to WASM (`data/lean_analyzer.wasm`) with `extern "C"` exports and an ES module wrapper (`js/lean_analyzer_bridge.js`).
- **Validation done against Lean 4.34.1 (`tests/test_lean_oracle.rs`)**: Checked against a 20,311-row ground-truth oracle generated directly by Lean (`tools/gen_oracle.lean`): 41,292 point exactness checks, 4,304,660 interval soundness checks, and 127,999 congruence/reduction checks.
- **Microsecond `.ilean` Streaming Indexer (`batch_scanner.rs`, `ilean_parser.rs`)**: Zero-copy memory-mapped `.ilean` symbol, module, and declaration range scanner with incremental mtime tracking (`DaemonIndexTracker`).

## Quick Start

```bash
# 1. Run the Rust test and differential oracle suite (72 tests across 6 suites)
cargo test

# 2. Verify the Lean 4 formal soundness proofs (compiles in ~1.5s, no Mathlib needed)
cd lean && lake build

# 3. Build the WebAssembly binary (data/lean_analyzer.wasm)
bash scripts/build_and_sync_wasm.sh
```

## JavaScript / TypeScript Usage

```javascript
import { loadLeanAnalyzerBridge } from "./js/lean_analyzer_bridge.js";

const bridge = await loadLeanAnalyzerBridge();

// 1. Bitset sign lattice join (Zero=1 | Positive=2 -> NonNegative=3)
console.log(bridge.joinSigns(1, 2)); // 3

// 2. Mutual Granger reduction: [1, 299] intersect (0 mod 100) -> [100, 200]
console.log(bridge.reduceIntervalCongruence(1, 299, 100, 0));
// { min: 100, max: 200, stride: 100, offset: 0 }

// 3. Zone DBM termination check: i - n <= -1 and step = 1 implies n - (i + 1) < n - i
console.log(bridge.checkZoneSubDecreasing(-1, 1)); // 2 (AbstractBool.True)

// 4. Two-variable Octagon reduction: v0 in [30, 100], v1 in [0, 100], v0 + v1 == 100
console.log(bridge.reduceOctagonTwoVars(30, 100, 0, 100, 100, 100));
// [ { min: 30, max: 100 }, { min: 0, max: 70 } ]
```

## License

Apache-2.0. See [LICENSE](LICENSE).
