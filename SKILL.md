# SKILL: translate a C++/Go/Solidity function into a Lean 4 model

This is the portable specification of the **C++→Lean translation skill** that
leanlift's untrusted front-end performs. It exists so the translation is
*reproducible by any agent* — `claude -p`, a local model (Gemma via ollama), a
remote model (Qwen on the RTX 6000 Pro box), or a human — not locked inside the
tool's inlined prompt. The `skill` lane (`lift verify --lane skill …`) drives the
translation from **this file**, proving it is self-sufficient.

The trust model is **"LLM proposes, algorithm disposes."** Your translation is a
*hypothesis*. leanlift wraps it in a runner, executes it on a deterministic
vector set, and the differential oracle either confirms it bit-for-bit (L1) or
hands back a structured failure to repair. You are never trusted; the Lean kernel
and the oracle are.

## Your task

Given a source function `f`, output **one Lean 4 `def`**, named exactly `f`, that
computes the same function over the audited support library. Nothing else.

## Output contract (strict)

- Output **only** the single `def` — no prose, no explanation, no `import`, no
  `open`, no `namespace`, no `end`, **no code fences**.
- Name it **exactly** as the source function.
- Use the **shape given in the prompt**, e.g. `def avg (x0 x1 : U32) : Res U32`
  or `def gss (x0 x1 x2 : Float) : Float`.
- Translate the arithmetic and control flow **op-for-op**. Do not "fix",
  saturate, clamp, or simplify — divergences are the point of the test.

(If your model emits a reasoning/thinking preamble or quotes the source in a
fence, the harness strips it and keeps the last block containing a `def` — but
prefer to emit just the `def`.)

## Target API — integers (`LeanLift.Checked`)

Already imported; `open LeanLift` is in scope. Models a fixed-width unsigned
machine integer whose arithmetic is **checked**: any result outside `[0, 2^W)`
yields `Res.fail` instead of wrapping (this is exactly where C/C++ diverge).

```
inductive Res (α) | ok (v : α) | fail        -- a Monad: pure / do / ← work
structure UInt (width : Nat) where val : Nat -- abbrevs: U8 U16 U32 U64
UInt.ofNat (width n : Nat) : Res (UInt width) -- range-checked injection
UInt.lit  (n : Nat) : UInt width              -- literal (width inferred)
UInt.le / UInt.ge (a b : UInt w) : Bool       -- comparisons
UInt.add / UInt.sub / UInt.mul (a b : UInt w) : Res (UInt w) -- CHECKED: fail on over/underflow
UInt.div (a b : UInt w) : Res (UInt w)        -- CHECKED: fail on div-by-zero
```

Use `do` / `←` to sequence the checked operations. Checked ops **fail where C/C++
wrap** — leave that; do not add saturation.

## Target API — floats (`LeanLift.Float`)

Already imported; `open LeanLift` is in scope. Lean's native IEEE-754 **binary64**
`Float`, which is *correctly rounded* on the basic ops, so it matches C++ `double`
(compiled `-ffp-contract=off`) **bit-for-bit**. There is **no `Res` monad** —
floats never `fail`; NaN/Inf are handled by the runner's canonicalization.

```
+  -  *  /            -- the basic ops (Float.add/sub/mul/div), correctly rounded
Float.sqrt a          -- correctly-rounded square root
a < b   a <= b   a == b      -- comparisons, returning Bool
0.5, 2.0, 3.0, …      -- Float literals (decimal)
Float.iterate (n : Nat) (f : σ → σ) (s : σ) : σ   -- a BOUNDED loop (n steps)
```

Rules for the float path:

- Use **only** `+ - * /`, `Float.sqrt`, and comparisons. **No transcendentals**
  (`exp`/`log`/`sin`/`pow`) — they are not bit-reproducible.
- Express every loop with `Float.iterate` (a fixed step count) or structural
  recursion — no `partial`, no unbounded `while`. A `break` on a tolerance is
  modeled by making the step the **identity** once the tolerance is met.
- Reproduce irrational constants by **arithmetic on `Float.sqrt`**, never as a
  truncated decimal literal: e.g. `let invphi := (Float.sqrt 5.0 - 1.0) / 2.0`.
- Carry multi-variable loop state as a tuple, e.g.
  `Float.iterate 200 step (x0, y0)`; read components with `.1` / `.2.1` / ….

## The repair protocol

If your translation is wrong, you receive a **structured failure**. Return the
**corrected single `def`** (same contract). Two failure kinds:

1. **Lean rejected your definition** — an elaboration/typecheck error excerpt.
   Fix the syntax/types to match the API above.
2. **Counterexample** — `On input (…), the C++ reference returns X but your model
   returns Y.` Re-derive the arithmetic op-for-op so the two agree exactly.
   (Integer results match directly; float results are compared as IEEE-754 bit
   patterns, `NAN` being the canonical NaN, `OVERFLOW` the checked-integer
   failure.)

## Worked examples

Integer — the midpoint average (the `add` may overflow u32, which is intended):

```
def avg (x0 x1 : U32) : Res U32 := do
  let s ← UInt.add x0 x1
  UInt.div s (UInt.lit 2)
```

Float — golden-section search (bounded loop, computed constants, identity step on
the tolerance):

```
def gss (x0 x1 x2 : Float) : Float :=
  let invphi := (Float.sqrt 5.0 - 1.0) / 2.0
  let invphi2 := (3.0 - Float.sqrt 5.0) / 2.0
  let step := fun (ab : Float × Float) =>
    let a := ab.1; let b := ab.2
    let h := b - a
    if h ≤ x2 then (a, b)
    else
      let c := a + invphi2 * h
      let d := a + invphi * h
      if (c - 3.0) * (c - 3.0) + 1.0 < (d - 3.0) * (d - 3.0) + 1.0 then (a, d) else (c, b)
  let r := Float.iterate 100 step (x0, x1)
  (r.1 + r.2) / 2.0
```

---

This file is the single source of truth for the prompt; `src/harness.rs` mirrors
the two API blurbs (`SUPPORT_API`, `FLOAT_API`). Keep them in sync.
