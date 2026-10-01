-- Proof obligations for the order-book bitmap scans `best_bid`
-- (PLAN-concurrency E1: the SC-only #9 order book in safe Rust, Charon+Aeneas
-- extracted). The engine prepends `import Aeneas`, the opens, `namespace
-- kernel`, and the freshly-EXTRACTED defs, then appends `end kernel`.
--
-- These are the bit-scan refinement that leanlift-iris's Phase A3
-- (`PhaseA/OrderBook.lean`) left as a separate obligation: there `maxOcc` /
-- `minOcc` are the greatest / least occupied tick of an abstract ladder; here a
-- 64-tick ladder is an occupancy word `occ`, tick `j` is occupied iff bit `j`
-- is set, and the extracted loops are proved to return exactly the highest /
-- lowest set bit, or 64 when no tick is occupied — the shape of
-- `maxOcc_some_iff` / `minOcc_some_iff` over this ladder.
--
-- Recipe as `isqrt`: `loop.spec_decr_nat` with an explicit measure and
-- invariant. The shift amount stays below 64 throughout, which is the
-- side-condition the extracted `>>>` carries.

/-- Bit `i` of `x`, the way the kernels test it. -/
theorem bit_iff (x i : Nat) : (x >>> i) &&& 1 = 1 ↔ x.testBit i := by
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp

theorem best_bid_spec (occ : Std.U64) :
    best_bid occ ⦃ r =>
      r.val ≤ 64
      ∧ (r.val = 64 → ∀ j, j < 64 → ¬ occ.val.testBit j)
      ∧ (r.val < 64 → occ.val.testBit r.val ∧ ∀ j, r.val < j → j < 64 → ¬ occ.val.testBit j) ⦄ := by
  unfold best_bid best_bid_loop
  apply loop.spec_decr_nat
    (measure := fun x => x.1.val)
    (inv := fun x => x.1.val ≤ 64
      ∧ (x.2.val = 64 → ∀ j, x.1.val ≤ j → j < 64 → ¬ occ.val.testBit j)
      ∧ (x.2.val ≠ 64 → x.2.val = x.1.val ∧ occ.val.testBit x.2.val
            ∧ ∀ j, x.2.val < j → j < 64 → ¬ occ.val.testBit j))
  · rintro ⟨i, found⟩ ⟨hi, hnone, hsome⟩
    simp only at hi hnone hsome
    simp only [best_bid_loop.body]
    split
    · rename_i hpos
      split
      · rename_i hf
        have hf' : found.val = 64 := by scalar_tac
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2, _⟩
        simp only [Aeneas.Std.lift, bind_ok]
        split
        · rename_i hb
          have hbit : occ.val.testBit i1.val := by
            have : (i2 &&& 1#u64).val = 1 := by rw [hb]; rfl
            rw [UScalar.val_and, hi2] at this
            exact (bit_iff _ _).mp (by simpa using this)
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨by scalar_tac, fun h => absurd h (by scalar_tac), fun _ => ⟨by simp, hbit, ?_⟩, by scalar_tac⟩
          intro j hj hj64
          exact hnone hf' j (by scalar_tac) hj64
        · rename_i hb
          have hnbit : ¬ occ.val.testBit i1.val := by
            intro ht
            apply hb
            have : (occ.val >>> i1.val) &&& 1 = 1 := (bit_iff _ _).mpr ht
            apply UScalar.eq_of_val_eq
            rw [UScalar.val_and, hi2]
            simpa using this
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨by scalar_tac, fun _ j hj hj64 => ?_, fun h => absurd hf' h, by scalar_tac⟩
          by_cases hji : j = i1.val
          · subst hji; exact hnbit
          · exact hnone hf' j (by scalar_tac) hj64
      · rename_i hf
        have hf' : found.val ≠ 64 := by intro h; apply hf; scalar_tac
        obtain ⟨heq, hbit, habove⟩ := hsome hf'
        simp only [Aeneas.Std.WP.spec_ok]
        exact ⟨by scalar_tac, fun h => absurd h hf', fun _ => ⟨hbit, habove⟩⟩
    · rename_i hz
      have hi0 : i.val = 0 := by scalar_tac
      simp only [Aeneas.Std.WP.spec_ok]
      by_cases hf : found.val = 64
      · exact ⟨by scalar_tac, fun _ j hj => hnone hf j (by omega) hj, fun h => absurd hf (by omega)⟩
      · obtain ⟨heq, hbit, habove⟩ := hsome hf
        exact ⟨by scalar_tac, fun h => absurd h hf, fun _ => ⟨hbit, habove⟩⟩
  · exact ⟨by scalar_tac, fun _ j hj hj64 => absurd hj64 (by scalar_tac),
      fun h => absurd (by scalar_tac) h⟩

/-- **The spec pins the answer.** Ticks 5 and 7 occupied (`occ = 160`): the
    best bid is exactly 7. Not a weaker "r ≤ 64" — the characterisation leaves
    one possible value, and this instance shows it is the right one. -/
theorem best_bid_160 : best_bid 160#u64 ⦃ r => r.val = 7 ⦄ := by
  apply WP.spec_mono (best_bid_spec 160#u64)
  rintro r ⟨hle, hnone, hsome⟩
  have h7 : (160 : Nat).testBit 7 = true := by decide
  have hlt : r.val < 64 := by
    rcases Nat.lt_or_ge r.val 64 with h | h
    · exact h
    · exact absurd h7 (hnone (by omega) 7 (by omega))
  obtain ⟨hbit, habove⟩ := hsome hlt
  have hall : ∀ k, k < 64 → (160 : Nat).testBit k = true → k = 5 ∨ k = 7 := by decide
  rcases hall r.val hlt (by simpa using hbit) with h | h
  · exact absurd h7 (habove 7 (by omega) (by omega))
  · exact h

#print axioms best_bid_spec
#print axioms best_bid_160
