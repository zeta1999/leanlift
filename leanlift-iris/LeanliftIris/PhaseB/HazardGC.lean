/-
Phase B (step 8b) — hazard-pointer **bounded-garbage accounting** (`#7`).

`HazardPtr.lean` proved the *safety* side: under seq_cst the publish/revalidate ∥
retire/scan handshake never lets a reader dereference a freed node. The other half
of the hazard-pointer guarantee is **progress / space**: retired-but-not-yet-freed
nodes (garbage) are *bounded*, so memory does not blow up. This file is that
accounting, as a self-contained combinatorial argument (no weak memory needed — it
is about how many nodes a scan can fail to reclaim).

The mechanism: each of `N` reader threads owns `K` hazard slots; a node is
**hazardous** (un-freeable) exactly when it sits in some occupied slot. A
reclaimer scans its private retire list and frees every node that is *not*
hazardous. So:

  * at most `N · K` nodes are hazardous at once (`allSlots_length_le`), hence
  * a scan leaves at most `N · K` nodes unreclaimed (`bounded_garbage`) — the
    garbage bound, proved by pigeonhole (distinct survivors ⊆ the slot list), and
  * a scan of `R` retired nodes frees at least `R − N·K` of them
    (`reclaim_progress`) — so once `R > N·K` every scan makes progress, and the
    retire list cannot grow without bound.

Core Lean only, sorry-free.
-/
namespace LeanliftIris.PhaseB

/-- A reclaimable object, identified by its address. -/
abbrev Node := Nat

namespace HazardGC

/-! ## A pigeonhole lemma: a duplicate-free list inside another is no longer

(The one general fact the bound rests on; proved from scratch to stay Mathlib-free.) -/

/-- If `l` has no duplicates and every element of `l` is in `m`, then `l` is no
longer than `m`. -/
theorem length_le_of_subset_nodup {α : Type} [DecidableEq α] :
    ∀ {l m : List α}, l ⊆ m → l.Nodup → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intro m _ _; exact Nat.zero_le _
  | cons a l ih =>
      intro m hsub hnd
      have ham : a ∈ m := hsub List.mem_cons_self
      have hanl : a ∉ l := (List.nodup_cons.mp hnd).1
      have hndl : l.Nodup := (List.nodup_cons.mp hnd).2
      have hsub' : l ⊆ m.erase a := by
        intro b hb
        have hbm : b ∈ m := hsub (List.mem_cons_of_mem a hb)
        have hba : b ≠ a := fun h => hanl (h ▸ hb)
        exact (List.mem_erase_of_ne hba).mpr hbm
      have hlen : l.length ≤ (m.erase a).length := ih hsub' hndl
      have herase : (m.erase a).length = m.length - 1 := List.length_erase_of_mem ham
      have hpos : 0 < m.length := List.length_pos_of_mem ham
      simp only [List.length_cons]; omega

/-! ## The static slot bound: at most `N · K` nodes are hazardous -/

/-- A linear-sum bound: if every entry is `≤ K`, the sum is `≤ (#entries) · K`. -/
theorem sum_le_length_mul {K : Nat} :
    ∀ (L : List Nat), (∀ x ∈ L, x ≤ K) → L.sum ≤ L.length * K := by
  intro L
  induction L with
  | nil => intro _; exact Nat.zero_le _
  | cons a l ih =>
      intro h
      have ha : a ≤ K := h a List.mem_cons_self
      have hl : l.sum ≤ l.length * K := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

/-- The global hazard array as the concatenation of each reader's occupied slots. -/
def allSlots (readers : List (List Node)) : List Node := readers.flatten

/-- **At most `N · K` slots.** With `N` readers each holding at most `K` hazard
pointers, the global hazard array has at most `N · K` entries. -/
theorem allSlots_length_le (readers : List (List Node)) (K : Nat)
    (h : ∀ r ∈ readers, r.length ≤ K) :
    (allSlots readers).length ≤ readers.length * K := by
  unfold allSlots
  rw [List.length_flatten]
  have : (readers.map List.length).sum ≤ (readers.map List.length).length * K := by
    apply sum_le_length_mul
    intro x hx
    rcases List.mem_map.mp hx with ⟨r, hr, hxr⟩
    rw [← hxr]; exact h r hr
  rwa [List.length_map] at this

/-! ## The scan: free every node that is not hazardous -/

/-- The **survivors** of a scan: retired nodes still protected by some hazard slot
(`slots` is the global hazard array). The reclaimer frees the rest. -/
def survivors (retired slots : List Node) : List Node :=
  retired.filter (fun n => decide (n ∈ slots))

/-- The number of nodes a scan reclaims. -/
def numReclaimed (retired slots : List Node) : Nat :=
  retired.length - (survivors retired slots).length

/-- A survivor is in the retire list and is hazardous. -/
theorem mem_survivors {retired slots : List Node} {n : Node} :
    n ∈ survivors retired slots ↔ n ∈ retired ∧ n ∈ slots := by
  simp [survivors, List.mem_filter]

/-- **Scan soundness.** Every node that survives a scan is hazardous — the
reclaimer only ever keeps nodes some reader still protects. -/
theorem survivor_hazardous {retired slots : List Node} {n : Node}
    (h : n ∈ survivors retired slots) : n ∈ slots :=
  (mem_survivors.mp h).2

/-- The survivors are a sub-list of the hazard array. -/
theorem survivors_subset_slots (retired slots : List Node) :
    survivors retired slots ⊆ slots :=
  fun _ h => survivor_hazardous h

/-! ## The garbage bound and reclamation progress -/

/-- **Bounded garbage.** After a scan, the number of unreclaimed (still-retired)
nodes is at most the number of hazard slots `N · K`. Pigeonhole: the survivors are
distinct (each node retired once) and all hazardous, so they inject into the slot
list. So garbage never exceeds the static slot budget. -/
theorem bounded_garbage (retired slots : List Node) (hnd : retired.Nodup) :
    (survivors retired slots).length ≤ slots.length :=
  length_le_of_subset_nodup (survivors_subset_slots retired slots)
    (hnd.filter (fun n => decide (n ∈ slots)))

/-- **Bounded garbage, quantitative.** Stated against the `N · K` static budget. -/
theorem bounded_garbage_NK (retired : List Node) (readers : List (List Node)) (K : Nat)
    (hnd : retired.Nodup) (hK : ∀ r ∈ readers, r.length ≤ K) :
    (survivors retired (allSlots readers)).length ≤ readers.length * K :=
  Nat.le_trans (bounded_garbage retired (allSlots readers) hnd)
    (allSlots_length_le readers K hK)

/-- **Reclamation progress.** A scan of `R` retired nodes frees at least
`R − N·K` of them. So whenever the retire list exceeds the slot budget the scan
strictly shrinks it — the retire list cannot grow without bound. -/
theorem reclaim_progress (retired slots : List Node) (hnd : retired.Nodup) :
    retired.length - slots.length ≤ numReclaimed retired slots := by
  have h := bounded_garbage retired slots hnd
  unfold numReclaimed
  omega

end HazardGC

end LeanliftIris.PhaseB
