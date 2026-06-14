-- Proof obligations for `fire_place` (PLAN-verification §V3 — the Aeneas
-- dogfood), over the Aeneas-EXTRACTED `Result Std.U32` model of leanlift's OWN
-- Petri firing kernel `m - pre + post`. The engine prepends `import Aeneas`,
-- the opens, `namespace kernel`, and the freshly-extracted `def fire_place …`,
-- then appends `end kernel`; these theorems are proved about that exact
-- extracted definition.
--
-- They are the CONCRETE `Std.U32` instances of the abstract theorems in
-- lean/LeanLift/Models/Petri.lean — `fire_le` (a non-increasing enabled
-- transition cannot raise the per-place count) and `le_preserved` (an upper
-- bound survives such a transition). Proving them about the *extracted* code
-- closes the loop: leanlift's Charon+Aeneas pipeline certifies the very kernel
-- that production `PtNet::step` runs (`src/models/ir.rs::fire_place`).
--
-- The `Result` monad makes each u32 op fallible; the premises are exactly the
-- side-conditions that make firing total: `pre ≤ m` (enabled ⇒ no subtraction
-- underflow) and `post ≤ pre` (non-increasing ⇒ the `+ post` cannot overflow,
-- since the result is ≤ m ≤ U32.max).

-- fire_le (concrete u32): firing cannot increase the per-place count.
theorem fire_place_le (m pre post : Std.U32)
    (hen : pre.val ≤ m.val) (hnp : post.val ≤ pre.val) :
    fire_place m pre post ⦃ r => r.val ≤ m.val ⦄ := by
  unfold fire_place
  step as ⟨ i, hi ⟩      -- i = m - pre   (enabled ⇒ no underflow)
  step as ⟨ r, hr ⟩      -- r = i + post  (≤ m ⇒ no overflow)
  all_goals scalar_tac

-- le_preserved (concrete u32): an upper bound m ≤ k survives the transition.
theorem fire_place_le_k (m pre post : Std.U32) (k : Nat)
    (hen : pre.val ≤ m.val) (hnp : post.val ≤ pre.val) (hk : m.val ≤ k) :
    fire_place m pre post ⦃ r => r.val ≤ k ⦄ := by
  unfold fire_place
  step as ⟨ i, hi ⟩
  step as ⟨ r, hr ⟩
  all_goals scalar_tac

#print axioms fire_place_le
#print axioms fire_place_le_k
