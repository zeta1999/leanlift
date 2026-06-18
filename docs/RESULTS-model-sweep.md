# Local-model translation sweep — gemma4 {e4b,12b,26b} + qwen3.6

> **⚠️ PRELIMINARY RESULTS — ZERO HARNESS ENGINEERING.** These numbers are a
> first, raw baseline: the stock prompt, the stock 4-iteration repair loop, and
> default model settings, with **no** prompt tuning, no few-shot examples, no
> support-lib API hints, no sampling/temperature sweeps, and no per-model
> adaptation. They measure the models "out of the box" against the existing
> harness — not the ceiling of what these models can do here. Further
> tests and harness work are underway; expect these pass rates to move.

Run date: 2026-06-18. Box: RTX PRO 6000 Blackwell (97 GB VRAM). Driver: ollama
0.30.9. Lean 4.31.0 (elan). forge 1.7.1. Reproduce with `scripts/gemma-sweep.sh`.

The sweep runs the 11 LLM-lane examples (the `Frontend::Llm` translation tests in
`src/examples.rs`) through four local models and records, per cell, the verdict
and the **effective context** the model actually consumed.

- **Verdict** — `L1 conformant/N` = candidate typechecked *and* matched the
  source bit-exactly on N differential vectors; `L0 FAILED` = candidate never
  typechecked, even after the 4-iteration propose→difftest→repair loop.
- **ptoks / otoks** — peak prompt tokens / max output tokens across the loop's
  calls, from ollama's `prompt_eval_count` / `eval_count` (see the instrumented
  `run_ollama` in `src/harness.rs`).
- **num_ctx = 32768** for every run (`LEANLIFT_NUM_CTX`). `trunc` = whether any
  call hit the window. All cells: `no`.

## Conformance matrix

| Test          | gemma4:e4b | gemma4:12b | gemma4:26b | qwen3.6:35b-a3b |
|---------------|:----------:|:----------:|:----------:|:---------------:|
| cpp-fadd      | ✅ | ✅ | ✅ | ✅ |
| sol-dot2      | ✗  | ✅ | ✅ | ✅ |
| cpp-dot2      | ✗  | ✗  | ✅ | ✗  |
| go-avg        | ✗  | ✗  | ✅ | ✗  |
| cpp-streamed  | ✗  | ✗  | ✗  | ✗  |
| cpp-isqrt     | ✗  | ✗  | ✗  | ✗  |
| cpp-bisect    | ✗  | ✗  | ✗  | ✗  |
| cpp-quant     | ✗  | ✗  | ✗  | ✗  |
| cpp-opt-gss   | ✗  | ✗  | ✗  | ✗  |
| cpp-opt-gd    | ✗  | ✗  | ✗  | ✗  |
| cpp-opt-hj    | ✗  | ✗  | ✗  | ✗  |
| **Passed**    | **1/11** | **2/11** | **4/11** | **2/11** |

## Per-model detail (verdict · iters · peak ptoks · max otoks)

### gemma4:e4b — lane gemma (1/11)
| test | verdict | iters | ptoks | otoks |
|------|---------|:-----:|:-----:|:-----:|
| cpp-streamed | L0 FAILED | 4 | 1447 | 687 |
| cpp-dot2     | L0 FAILED | 4 | 694  | 46  |
| go-avg       | L0 FAILED | 4 | 588  | 42  |
| sol-dot2     | L0 FAILED | 4 | 674  | 63  |
| cpp-isqrt    | L0 FAILED | 4 | 966  | 274 |
| cpp-bisect   | L0 FAILED | 4 | 1301 | 573 |
| cpp-quant    | L0 FAILED | 4 | 1288 | 313 |
| cpp-fadd     | L1 conformant/209 | 1 | 547 | 20 |
| cpp-opt-gss  | L0 FAILED | 4 | 3267 | 2237 |
| cpp-opt-gd   | L0 FAILED | 4 | 1004 | 200 |
| cpp-opt-hj   | L0 FAILED | 4 | 4796 | 3438 |

### gemma4:12b — lane gemma (2/11)
| test | verdict | iters | ptoks | otoks |
|------|---------|:-----:|:-----:|:-----:|
| cpp-streamed | L0 FAILED | 4 | 831  | 108 |
| cpp-dot2     | L0 FAILED | 4 | 707  | 55  |
| go-avg       | L0 FAILED | 4 | 588  | 38  |
| sol-dot2     | L1 conformant/247 | 1 | 640 | 57 |
| cpp-isqrt    | L0 FAILED | 4 | 1042 | 359 |
| cpp-bisect   | L0 FAILED | 4 | 833  | 129 |
| cpp-quant    | L0 FAILED | 4 | 1870 | 721 |
| cpp-fadd     | L1 conformant/209 | 1 | 551 | 22 |
| cpp-opt-gss  | L0 FAILED | 4 | 1214 | 249 |
| cpp-opt-gd   | L0 FAILED | 4 | 969  | 161 |
| cpp-opt-hj   | L0 FAILED | 4 | 2070 | 865 |

### gemma4:26b — lane gemma (4/11)
| test | verdict | iters | ptoks | otoks |
|------|---------|:-----:|:-----:|:-----:|
| cpp-streamed | L0 FAILED | 4 | 849  | 116 |
| cpp-dot2     | L1 conformant/247 | 1 | 677 | 57 |
| go-avg       | L1 conformant/248 | 1 | 575 | 43 |
| sol-dot2     | L1 conformant/247 | 1 | 640 | 49 |
| cpp-isqrt    | L0 FAILED | 4 | 849  | 157 |
| cpp-bisect   | L0 FAILED | 4 | 888  | 184 |
| cpp-quant    | L0 FAILED | 4 | 3192 | 1826 |
| cpp-fadd     | L1 conformant/209 | 1 | 551 | 20 |
| cpp-opt-gss  | L0 FAILED | 4 | 1493 | 504 |
| cpp-opt-gd   | L0 FAILED | 4 | 1004 | 196 |
| cpp-opt-hj   | L0 FAILED | 4 | 1817 | 649 |

### qwen3.6:35b-a3b-bf16 — lane ollama (2/11)
| test | verdict | iters | ptoks | otoks |
|------|---------|:-----:|:-----:|:-----:|
| cpp-streamed | L0 FAILED | 4 | 801  | 95  |
| cpp-dot2     | L0 FAILED | 4 | —    | —   |
| go-avg       | L0 FAILED | 4 | 1052 | 486 |
| sol-dot2     | L1 conformant/247 | 1 | 631 | 57 |
| cpp-isqrt    | L0 FAILED | 4 | 834  | 176 |
| cpp-bisect   | L0 FAILED | 4 | 843  | 173 |
| cpp-quant    | L0 FAILED | 4 | 1225 | 480 |
| cpp-fadd     | L1 conformant/209 | 1 | 531 | 21 |
| cpp-opt-gss  | L0 FAILED | 4 | 1232 | 279 |
| cpp-opt-gd   | L0 FAILED | 4 | 957  | 165 |
| cpp-opt-hj   | L0 FAILED | 4 | 1759 | 579 |

(`cpp-dot2`/qwen shows `—` because that cell was served from `.leanlift-cache`
— a cache hit emits no fresh token counts.)

## Findings

- **Quality scales with gemma size**: e4b 1 → 12b 2 → 26b 4. `gemma4:26b` is the
  best local model and the only one to solve `cpp-dot2` and `go-avg`.
- **qwen3.6:35b-a3b (bf16)** lands at 2/11 — matches 12b, below 26b. The a3b MoE
  (≈3 B active) does not out-translate the dense 26b on these kernels.
- **`cpp-fadd` passes everywhere**; every conformant cell settles in **1
  iteration** (no model used the repair loop to recover). The 7 hard kernels
  (reductions, loops, the optimization ladder) fail for all four models.
- **No truncation, ever.** The largest prompt was e4b on `cpp-opt-hj` at 4796
  tokens (~15 % of the 32 768 window); the opt kernels are heaviest, the rest sit
  at 0.5k–3k. So the L0 failures are **genuine model capability, not lost
  context** — raising `num_ctx` will not help.

## Environment notes / caveats

- `go-avg` needs `GOFLAGS=-buildvcs=false` (Go VCS stamping fails with exit 128
  inside this git tree); the sweep script exports it. Without it the oracle build
  fails *before* any model runs, surfacing as `ERR(rc=1)`.
- gemma tags use ollama's default quant (e4b 9.6 GB, 12b 7.6 GB, 26b 17 GB); only
  qwen is explicitly bf16.
- Logs and per-cell `report.json` are written under `$OUT` (default
  `/tmp/leanlift-sweep`), not committed.
