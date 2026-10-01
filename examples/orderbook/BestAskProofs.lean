-- Proof obligations for the order-book bitmap scans `best_ask`
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

theorem best_ask_spec (occ : Std.U64) :
    best_ask occ ⦃ r =>
      r.val ≤ 64
      ∧ (r.val = 64 → ∀ j, j < 64 → ¬ occ.val.testBit j)
      ∧ (r.val < 64 → occ.val.testBit r.val ∧ ∀ j, j < r.val → ¬ occ.val.testBit j) ⦄ := by
  unfold best_ask best_ask_loop
  apply loop.spec_decr_nat
    (measure := fun x => 64 - x.1.val)
    (inv := fun x => x.1.val ≤ 64
      ∧ (x.2.val = 64 → ∀ j, j < x.1.val → ¬ occ.val.testBit j)
      ∧ (x.2.val ≠ 64 → x.2.val < x.1.val ∧ occ.val.testBit x.2.val
            ∧ ∀ j, j < x.2.val → ¬ occ.val.testBit j))
  · rintro ⟨i, found⟩ ⟨hi, hnone, hsome⟩
    simp only at hi hnone hsome
    simp only [best_ask_loop.body]
    split
    · rename_i hlt
      split
      · rename_i hf
        have hf' : found.val = 64 := by scalar_tac
        step as ⟨i1, hi1, _⟩
        simp only [Aeneas.Std.lift, bind_ok]
        split
        · rename_i hb
          have hbit : occ.val.testBit i.val := by
            have : (i1 &&& 1#u64).val = 1 := by rw [hb]; rfl
            rw [UScalar.val_and, hi1] at this
            exact (bit_iff _ _).mp (by simpa using this)
          step as ⟨i3, hi3⟩
          refine ⟨by scalar_tac, fun h => absurd h (by scalar_tac), fun _ => ⟨by scalar_tac, hbit, ?_⟩,
            by scalar_tac⟩
          intro j hj
          exact hnone hf' j hj
        · rename_i hb
          have hnbit : ¬ occ.val.testBit i.val := by
            intro ht
            apply hb
            have : (occ.val >>> i.val) &&& 1 = 1 := (bit_iff _ _).mpr ht
            apply UScalar.eq_of_val_eq
            rw [UScalar.val_and, hi1]
            simpa using this
          step as ⟨i3, hi3⟩
          refine ⟨by scalar_tac, fun _ j hj => ?_, fun h => absurd hf' h, by scalar_tac⟩
          by_cases hji : j = i.val
          · subst hji; exact hnbit
          · exact hnone hf' j (by scalar_tac)
      · rename_i hf
        have hf' : found.val ≠ 64 := by intro h; apply hf; scalar_tac
        obtain ⟨hlt', hbit, hbelow⟩ := hsome hf'
        simp only [Aeneas.Std.WP.spec_ok]
        exact ⟨by scalar_tac, fun h => absurd h hf', fun _ => ⟨hbit, hbelow⟩⟩
    · rename_i hge
      have hi64 : i.val = 64 := by scalar_tac
      simp only [Aeneas.Std.WP.spec_ok]
      by_cases hf : found.val = 64
      · exact ⟨by scalar_tac, fun _ j hj => hnone hf j (by omega), fun h => absurd hf (by omega)⟩
      · obtain ⟨hlt', hbit, hbelow⟩ := hsome hf
        exact ⟨by scalar_tac, fun h => absurd h hf, fun _ => ⟨hbit, hbelow⟩⟩
  · exact ⟨by scalar_tac, fun _ j hj => absurd hj (by scalar_tac), fun h => absurd (by scalar_tac) h⟩

/-- **The spec pins the answer.** Ticks 5 and 7 occupied: the best ask is
    exactly 5. -/
theorem best_ask_160 : best_ask 160#u64 ⦃ r => r.val = 5 ⦄ := by
  apply WP.spec_mono (best_ask_spec 160#u64)
  rintro r ⟨hle, hnone, hsome⟩
  have h5 : (160 : Nat).testBit 5 = true := by decide
  have hlt : r.val < 64 := by
    rcases Nat.lt_or_ge r.val 64 with h | h
    · exact h
    · exact absurd h5 (hnone (by omega) 5 (by omega))
  obtain ⟨hbit, hbelow⟩ := hsome hlt
  have hall : ∀ k, k < 64 → (160 : Nat).testBit k = true → k = 5 ∨ k = 7 := by decide
  rcases hall r.val hlt (by simpa using hbit) with h | h
  · exact h
  · exact absurd h5 (hbelow 5 (by omega))

#print axioms best_ask_spec
#print axioms best_ask_160
