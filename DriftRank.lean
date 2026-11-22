import UnitDiagonalMatching

/-!
# Full-translation-class rank, path lifting, and ordered matching for arbitrary nonzero drift

This module generalizes `UnitDiagonalRank` and `UnitDiagonalMatching` from the unit-diagonal
drift `(1, -1)` to an arbitrary nonzero full period drift `v = wordDrift P w ≠ (0, 0)`.

## Design of `lift` and `base`

For `v = (v.1, v.2) ≠ (0, 0)`, we choose the first coordinate if `v.1 ≠ 0` and the second
coordinate if `v.1 = 0`, and define

  `lift v p := if v.1 = 0 then p.2 / v.2 else p.1 / v.1`
  `base v p := addPoint p (scalePoint v (-lift v p))`

using Lean's Euclidean integer division `Int.ediv`. Because `Int.add_mul_ediv_right` gives
`(a + z * c) / c = a / c + z` for every `c ≠ 0` regardless of the sign of `c`, `lift` is
strictly equivariant under arbitrary integer multiples of `v` (`lift_add_scale`), `base` is
invariant (`base_add_scale`), and every subsequent theorem avoids coordinate division altogether.

## Sections

1. Translation-class structure: `SameClass`, `lift`, `base`, decomposition, and decidability.
2. Stable time and stable rank: `stableTime`, `priorPhases` characterization, `classPhases`,
   `stableRank`, order/successor characterizations, and rank bijection onto `[0, class size)`.
3. Path lifting and first return on `ContinuousPhasePath` for arbitrary nonzero `v`.
4. Ordered matching of directed phase departures and arrivals between translation classes.
5. Consistency with `UnitDiagonalRank` / `UnitDiagonalMatching` for `v = (1, -1)`, and
   non-vacuity on the standard 104-step highway (`standard_word_consistent`, drift `(-2, -2)`).
-/

namespace LangtonsAnt
namespace Drift

/-! ## 1. Full-translation-class structure -/

/-- Two grid points belong to the same `ℤ•v` translation class. -/
def SameClass (v p q : Point) : Prop :=
  ∃ z : Int, q = addPoint p (scalePoint v z)

/-- Canonical integer translation coordinate along a nonzero drift `v`. -/
def lift (v p : Point) : Int :=
  if v.1 = 0 then p.2 / v.2 else p.1 / v.1

/-- Canonical basepoint of `p`'s translation class `p + ℤ•v`. -/
def base (v p : Point) : Point :=
  addPoint p (scalePoint v (-lift v p))

private theorem scalePoint_zero (v : Point) : scalePoint v 0 = (0, 0) := by
  simp [scalePoint]

private theorem scalePoint_one (v : Point) : scalePoint v 1 = v := by
  apply Prod.ext <;> simp [scalePoint]

private theorem addPoint_scalePoint_add (v p : Point) (a b : Int) :
    addPoint (addPoint p (scalePoint v a)) (scalePoint v b) =
      addPoint p (scalePoint v (a + b)) := by
  apply Prod.ext <;> simp only [addPoint, scalePoint, Int.add_mul] <;> omega

private theorem move_addPoint_right (p q : Point) (d : Direction) :
    move (addPoint p q) d = addPoint (move p d) q := by
  cases d <;> apply Prod.ext <;> simp [move, addPoint] <;> omega

/-- Every point decomposes as its canonical basepoint plus `lift v p • v`. -/
theorem decomp (v p : Point) :
    p = addPoint (base v p) (scalePoint v (lift v p)) := by
  apply Prod.ext <;> simp only [base, addPoint, scalePoint, Int.neg_mul] <;> omega

/-- Shifting by `z • v` shifts `lift v` by `z` for any nonzero `v`. -/
theorem lift_add_scale {v : Point} (hv : v ≠ (0, 0)) (p : Point) (z : Int) :
    lift v (addPoint p (scalePoint v z)) = lift v p + z := by
  unfold lift
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := fun h => hv (Prod.ext hx h)
    simp only [hx, ite_true, addPoint, scalePoint]
    exact Int.add_mul_ediv_right p.2 z hy
  · simp only [hx, ite_false, addPoint, scalePoint]
    exact Int.add_mul_ediv_right p.1 z hx

theorem lift_add {v : Point} (hv : v ≠ (0, 0)) (p : Point) :
    lift v (addPoint p v) = lift v p + 1 := by
  simpa only [scalePoint_one] using lift_add_scale hv p 1

/-- Shifting by `z • v` leaves the canonical basepoint unchanged. -/
theorem base_add_scale {v : Point} (hv : v ≠ (0, 0)) (p : Point) (z : Int) :
    base v (addPoint p (scalePoint v z)) = base v p := by
  unfold base
  rw [lift_add_scale hv p z]
  apply Prod.ext <;>
    simp only [addPoint, scalePoint, Int.neg_add, Int.add_mul, Int.neg_mul] <;> omega

theorem base_add {v : Point} (hv : v ≠ (0, 0)) (p : Point) :
    base v (addPoint p v) = base v p := by
  simpa only [scalePoint_one] using base_add_scale hv p 1

theorem lift_base {v : Point} (hv : v ≠ (0, 0)) (p : Point) :
    lift v (base v p) = 0 := by
  unfold base
  rw [lift_add_scale hv p (-lift v p)]
  omega

theorem base_base {v : Point} (hv : v ≠ (0, 0)) (p : Point) :
    base v (base v p) = base v p := by
  unfold base
  rw [lift_add_scale hv p (-lift v p)]
  apply Prod.ext <;>
    simp only [addPoint, scalePoint, Int.neg_add, Int.add_mul, Int.neg_mul] <;> omega

theorem decomp_unique {v p b : Point} {z : Int} (hv : v ≠ (0, 0))
    (hb : base v b = b) (hp : p = addPoint b (scalePoint v z)) :
    base v p = b ∧ lift v p = z := by
  have hbase : base v p = b := by
    rw [hp, base_add_scale hv b z, hb]
  have hlb : lift v b = 0 := by
    have := lift_base hv b
    rwa [hb] at this
  have hlift : lift v p = z := by
    rw [hp, lift_add_scale hv b z, hlb]
    omega
  exact ⟨hbase, hlift⟩

/-- Two points lie in the same `ℤ•v` class iff they have the same canonical basepoint. -/
theorem sameClass_iff_base_eq (v p q : Point) :
    SameClass v p q ↔ base v p = base v q := by
  by_cases hv : v = (0, 0)
  · subst hv
    constructor
    · rintro ⟨z, hq⟩
      have he : q = p := by simpa [addPoint, scalePoint] using hq
      subst he
      rfl
    · intro hb
      have he : p = q := Prod.ext (by simpa [base, addPoint, scalePoint] using congrArg Prod.fst hb)
        (by simpa [base, addPoint, scalePoint] using congrArg Prod.snd hb)
      exact ⟨0, by simp [he, addPoint, scalePoint]⟩
  · constructor
    · rintro ⟨z, rfl⟩
      exact (base_add_scale hv p z).symm
    · intro hb
      refine ⟨lift v q - lift v p, ?_⟩
      have hx := congrArg Prod.fst hb
      have hy := congrArg Prod.snd hb
      simp only [base, addPoint, scalePoint, Int.neg_mul] at hx hy
      apply Prod.ext <;> simp only [addPoint, scalePoint, Int.sub_mul] <;> omega

instance (v : Point) : DecidableRel (SameClass v) :=
  fun p q => decidable_of_iff (base v p = base v q) (sameClass_iff_base_eq v p q).symm

theorem SameClass.refl (v p : Point) : SameClass v p p :=
  ⟨0, by simp [addPoint, scalePoint]⟩

theorem SameClass.symm {v p q : Point} (h : SameClass v p q) : SameClass v q p :=
  (sameClass_iff_base_eq v q p).mpr ((sameClass_iff_base_eq v p q).mp h).symm

theorem SameClass.trans {v p q r : Point}
    (h1 : SameClass v p q) (h2 : SameClass v q r) : SameClass v p r :=
  (sameClass_iff_base_eq v p r).mpr
    (((sameClass_iff_base_eq v p q).mp h1).trans ((sameClass_iff_base_eq v q r).mp h2))

theorem sameClass_base (v p : Point) : SameClass v (base v p) p :=
  ⟨lift v p, decomp v p⟩

theorem sameClass_add_scale_right (v p : Point) (z : Int) :
    SameClass v p (addPoint p (scalePoint v z)) :=
  ⟨z, rfl⟩

theorem sameClass_add_scale_left (v p : Point) (z : Int) :
    SameClass v (addPoint p (scalePoint v z)) p :=
  (sameClass_add_scale_right v p z).symm

theorem sameClass_eq_add_scale {v p q : Point} (h : SameClass v p q) :
    q = addPoint p (scalePoint v (lift v q - lift v p)) := by
  have hb := (sameClass_iff_base_eq v p q).mp h
  have hx := congrArg Prod.fst hb
  have hy := congrArg Prod.snd hb
  simp only [base, addPoint, scalePoint, Int.neg_mul] at hx hy
  apply Prod.ext <;> simp only [addPoint, scalePoint, Int.sub_mul] <;> omega

theorem lift_diff_of_eq_add_scale {v p q : Point} (hv : v ≠ (0, 0)) {z : Int}
    (h : q = addPoint p (scalePoint v z)) :
    lift v q - lift v p = z := by
  have hl := lift_add_scale hv p z
  rw [← h] at hl
  omega

theorem sameClass_move_iff (v p q : Point) (d : Direction) :
    SameClass v (move p d) (move q d) ↔ SameClass v p q := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    cases d <;>
      · have hx := congrArg Prod.fst hz
        have hy := congrArg Prod.snd hz
        simp only [move, addPoint, scalePoint] at hx hy
        apply Prod.ext <;> simp only [addPoint, scalePoint] <;> omega
  · rintro ⟨z, rfl⟩
    exact ⟨z, move_addPoint_right p (scalePoint v z) d⟩

/-! ## 2. Stable time, `priorPhases` characterization, and stable rank -/

/-- Stable time of phase `i` relative to drift `v` and period `P`. -/
def stableTime (v : Point) (P : Nat) (w : Nat → Bool) (i : Nat) : Int :=
  (i : Int) - (P : Int) * lift v (wordPos w i)

/-- Phases in `[0, P)` whose position lies in the translation class of `c`. -/
def classPhases (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) : List Nat :=
  (List.range P).filter (fun i => decide (SameClass v (wordPos w i) c))

/-- Zero-based visit rank within the translation class: count of earlier visits. -/
def stableRank (P : Nat) (w : Nat → Bool) (i : Nat) : Nat :=
  (priorPhases P w i).length

theorem mem_classPhases {v c : Point} {P i : Nat} {w : Nat → Bool} :
    i ∈ classPhases v P w c ↔ i < P ∧ SameClass v (wordPos w i) c := by
  simp [classPhases]

theorem classPhases_nodup (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) :
    (classPhases v P w c).Nodup :=
  List.nodup_range.filter _

theorem classPhases_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool)
    (h : SameClass v c₁ c₂) :
    classPhases v P w c₁ = classPhases v P w c₂ := by
  unfold classPhases
  apply List.filter_congr
  intro i _
  exact Bool.eq_iff_iff.mpr (by
    simp only [decide_eq_true_eq]
    exact ⟨fun h1 => h1.trans h, fun h2 => h2.trans h.symm⟩)

/-- `stableTime` is injective on all phases `< P` (and in particular within each class). -/
theorem stableTime_injective {v : Point} {P i j : Nat} {w : Nat → Bool}
    (hi : i < P) (hj : j < P)
    (h : stableTime v P w i = stableTime v P w j) : i = j := by
  apply (biTime_injective (k := -lift v (wordPos w i)) (l := -lift v (wordPos w j)) hi hj ?_).2
  simp only [Int.neg_mul, Int.mul_comm (lift v (wordPos w i)),
    Int.mul_comm (lift v (wordPos w j))]
  unfold stableTime at h
  omega

/-- Exact characterization of `priorPhases` by translation class and strict `stableTime` order. -/
theorem mem_priorPhases_iff_stableTime {v : Point} {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    j ∈ priorPhases P w i ↔
      j < P ∧ SameClass v (wordPos w j) (wordPos w i) ∧
        stableTime v P w j < stableTime v P w i := by
  have hvw : wordDrift P w ≠ (0, 0) := by rw [hd]; exact hv
  by_cases hj : j < P
  · rw [mem_priorPhases_iff_integer_period hvw hi hj]
    constructor
    · rintro ⟨k, ht, hp⟩
      have hp' : wordPos w i = addPoint (wordPos w j) (scalePoint v k) := by
        simpa only [biPeriodicPos, hd] using hp.symm
      have hk : k = lift v (wordPos w i) - lift v (wordPos w j) :=
        (lift_diff_of_eq_add_scale hv hp').symm
      rw [hk, Int.sub_mul, Int.mul_comm (lift v (wordPos w i)),
        Int.mul_comm (lift v (wordPos w j))] at ht
      exact ⟨hj, ⟨k, hp'⟩, by unfold stableTime; omega⟩
    · rintro ⟨_, hsc, ht⟩
      refine ⟨lift v (wordPos w i) - lift v (wordPos w j), ?_, ?_⟩
      · simp only [Int.sub_mul, Int.mul_comm (lift v (wordPos w i)),
          Int.mul_comm (lift v (wordPos w j))]
        unfold stableTime at ht
        omega
      · simp only [biPeriodicPos, hd]
        exact (sameClass_eq_add_scale hsc).symm
  · rw [mem_priorPhases hvw]
    simp [hj]

theorem consistentWord_stableRank_color {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hi : i < P) :
    w i = decide (stableRank P w i % 2 = 1) :=
  h.2.2 i hi

theorem priorPhases_eq_stableTime_filter {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i < P) (hc : SameClass v (wordPos w i) c) :
    priorPhases P w i =
      (classPhases v P w c).filter
        (fun j => decide (stableTime v P w j < stableTime v P w i)) := by
  unfold priorPhases classPhases
  rw [List.filter_filter]
  apply List.filter_congr
  intro j hj
  apply Bool.eq_iff_iff.mpr
  have hh := mem_priorPhases_iff_stableTime (j := j) hd hv hi
  have hjP := List.mem_range.mp hj
  simp only [priorPhases, List.mem_filter, List.mem_range, hjP, true_and] at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, hh]
  exact ⟨fun ⟨hsc, ht⟩ => ⟨ht, hsc.trans hc⟩, fun ⟨ht, hsc⟩ => ⟨hsc.trans hc.symm, ht⟩⟩

theorem stableRank_eq_count_lt {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i ∈ classPhases v P w c) :
    stableRank P w i =
      ((classPhases v P w c).filter
        (fun j => decide (stableTime v P w j < stableTime v P w i))).length := by
  obtain ⟨hiP, hic⟩ := mem_classPhases.mp hi
  unfold stableRank
  rw [priorPhases_eq_stableTime_filter hd hv hiP hic]

theorem stableRank_lt_of_stableTime_lt {v : Point} {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) (hj : j < P)
    (hc : SameClass v (wordPos w i) (wordPos w j))
    (ht : stableTime v P w i < stableTime v P w j) :
    stableRank P w i < stableRank P w j := by
  have hnot : i ∉ priorPhases P w i := by
    rw [mem_priorPhases_iff_stableTime hd hv hi]
    omega
  have hnd : (i :: priorPhases P w i).Nodup :=
    List.nodup_cons.mpr ⟨hnot, priorPhases_nodup P w i⟩
  have hs : i :: priorPhases P w i ⊆ priorPhases P w j := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact (mem_priorPhases_iff_stableTime hd hv hj).mpr ⟨hi, hc, ht⟩
    · rcases (mem_priorPhases_iff_stableTime hd hv hi).mp hk with ⟨hkP, hkc, hkt⟩
      exact (mem_priorPhases_iff_stableTime hd hv hj).mpr ⟨hkP, hkc.trans hc, by omega⟩
  have := hnd.length_le_of_subset hs
  simpa only [List.length_cons, stableRank, Nat.succ_le_iff] using this

theorem stableRank_lt_iff_stableTime_lt {v : Point} {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) (hj : j < P)
    (hc : SameClass v (wordPos w i) (wordPos w j)) :
    stableRank P w i < stableRank P w j ↔ stableTime v P w i < stableTime v P w j := by
  refine ⟨?_, stableRank_lt_of_stableTime_lt hd hv hi hj hc⟩
  intro hr
  by_cases ht : stableTime v P w i < stableTime v P w j
  · exact ht
  · by_cases he : stableTime v P w i = stableTime v P w j
    · have := stableTime_injective hi hj he
      subst j
      omega
    · have := stableRank_lt_of_stableTime_lt hd hv hj hi hc.symm (by omega)
      omega

theorem stableRank_succ_iff {v : Point} {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) (hj : j < P)
    (hc : SameClass v (wordPos w i) (wordPos w j)) :
    stableRank P w j = stableRank P w i + 1 ↔
      stableTime v P w i < stableTime v P w j ∧
      ¬ ∃ k, k < P ∧ SameClass v (wordPos w k) (wordPos w i) ∧
        stableTime v P w i < stableTime v P w k ∧ stableTime v P w k < stableTime v P w j := by
  constructor
  · intro hr
    refine ⟨(stableRank_lt_iff_stableTime_lt hd hv hi hj hc).mp (by omega), ?_⟩
    rintro ⟨k, hk, hkc, hik, hkj⟩
    have := stableRank_lt_of_stableTime_lt hd hv hi hk hkc.symm hik
    have := stableRank_lt_of_stableTime_lt hd hv hk hj (hkc.trans hc) hkj
    omega
  · rintro ⟨ht, hgap⟩
    have hnot : i ∉ priorPhases P w i := by
      rw [mem_priorPhases_iff_stableTime hd hv hi]
      omega
    have hp : (priorPhases P w j).Perm (i :: priorPhases P w i) := by
      apply (List.perm_ext_iff_of_nodup (priorPhases_nodup P w j)
        (List.nodup_cons.mpr ⟨hnot, priorPhases_nodup P w i⟩)).mpr
      intro k
      rw [List.mem_cons, mem_priorPhases_iff_stableTime hd hv hj,
        mem_priorPhases_iff_stableTime hd hv hi]
      constructor
      · rintro ⟨hk, hkc, hkt⟩
        by_cases he : stableTime v P w k = stableTime v P w i
        · exact Or.inl (stableTime_injective hk hi he)
        · right
          refine ⟨hk, hkc.trans hc.symm, ?_⟩
          have : ¬ stableTime v P w i < stableTime v P w k :=
            fun h => hgap ⟨k, hk, hkc.trans hc.symm, h, hkt⟩
          omega
      · rintro (rfl | ⟨hk, hkc, hkt⟩)
        · exact ⟨hi, hc, ht⟩
        · exact ⟨hk, hkc.trans hc, by omega⟩
    exact hp.length_eq

private theorem nodup_map_on {α β : Type} {xs : List α} {f : α → β}
    (hn : xs.Nodup)
    (hf : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨b, hb, he⟩ := List.mem_map.mp h
      have := hf b (by simp [hb]) a (by simp) he
      subst b
      exact ha hb
    · exact ih hn (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy]))

theorem stableRank_lt_class_length {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i ∈ classPhases v P w c) :
    stableRank P w i < (classPhases v P w c).length := by
  obtain ⟨hiP, hic⟩ := mem_classPhases.mp hi
  have hn : (i :: priorPhases P w i).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, priorPhases_nodup P w i⟩
    simp [mem_priorPhases_iff_stableTime hd hv hiP]
  have hs : i :: priorPhases P w i ⊆ classPhases v P w c := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · obtain ⟨hjP, hjc, _⟩ := (mem_priorPhases_iff_stableTime hd hv hiP).mp hj
      exact mem_classPhases.mpr ⟨hjP, hjc.trans hic⟩
  have := hn.length_le_of_subset hs
  simpa only [List.length_cons, stableRank, Nat.succ_le_iff] using this

theorem stableRank_injective_on_class {v c : Point} {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ classPhases v P w c) (hj : j ∈ classPhases v P w c)
    (he : stableRank P w i = stableRank P w j) : i = j := by
  obtain ⟨hiP, hic⟩ := mem_classPhases.mp hi
  obtain ⟨hjP, hjc⟩ := mem_classPhases.mp hj
  have h1 := stableRank_lt_iff_stableTime_lt hd hv hiP hjP (hic.trans hjc.symm)
  have h2 := stableRank_lt_iff_stableTime_lt hd hv hjP hiP (hjc.trans hic.symm)
  apply stableTime_injective (v := v) (w := w) hiP hjP
  omega

theorem stableRank_surjective_on_class {v c : Point} {P r : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hr : r < (classPhases v P w c).length) :
    ∃ i ∈ classPhases v P w c, stableRank P w i = r := by
  let xs := (classPhases v P w c).map (stableRank P w)
  have hn : xs.Nodup := nodup_map_on (classPhases_nodup v P w c)
    (fun _ hi _ hj => stableRank_injective_on_class hd hv hi hj)
  have hs : xs ⊆ List.range (classPhases v P w c).length := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (stableRank_lt_class_length hd hv hi)
  have hm : r ∈ xs := by
    by_cases hnot : r ∈ xs
    · exact hnot
    apply False.elim
    have hn' := List.nodup_cons.mpr ⟨hnot, hn⟩
    have hs' : r :: xs ⊆ List.range (classPhases v P w c).length := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_range.mpr hr
      · exact hs hx
    have hh := hn'.length_le_of_subset hs'
    simp only [List.length_cons, List.length_range, xs, List.length_map] at hh
    omega
  exact List.mem_map.mp hm

/-- `stableRank` is a bijection from `classPhases v P w c` onto `[0, class size)`. -/
theorem stableRank_bijection_on_class {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    (∀ i ∈ classPhases v P w c, stableRank P w i < (classPhases v P w c).length) ∧
    (∀ i ∈ classPhases v P w c, ∀ j ∈ classPhases v P w c,
      stableRank P w i = stableRank P w j → i = j) ∧
    (∀ r, r < (classPhases v P w c).length →
      ∃ i ∈ classPhases v P w c, stableRank P w i = r) :=
  ⟨fun _ hi => stableRank_lt_class_length hd hv hi,
   fun _ hi _ hj => stableRank_injective_on_class hd hv hi hj,
   fun _ hr => stableRank_surjective_on_class hd hv hr⟩

theorem stableRank_map_perm_range {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    ((classPhases v P w c).map (stableRank P w)).Perm
      (List.range (classPhases v P w c).length) := by
  have hn : ((classPhases v P w c).map (stableRank P w)).Nodup :=
    nodup_map_on (classPhases_nodup v P w c)
      (fun _ hi _ hj => stableRank_injective_on_class hd hv hi hj)
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr
  intro r
  rw [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact stableRank_lt_class_length hd hv hi
  · exact stableRank_surjective_on_class hd hv

/-! ## 3. Path lifting and first return for arbitrary nonzero drift -/

theorem path_sameClass_pos {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (r : Nat) :
    SameClass v (wordPos w (p.phase r)) (p.pos w r) :=
  ⟨p.period r, by simp [ContinuousPhasePath.pos, biPeriodicPos, hd]⟩

theorem path_base_pos {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (r : Nat) :
    base v (p.pos w r) = base v (wordPos w (p.phase r)) :=
  ((sameClass_iff_base_eq v _ _).mp (path_sameClass_pos p hd r)).symm

theorem path_lift_pos {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (r : Nat) :
    lift v (p.pos w r) = lift v (wordPos w (p.phase r)) + p.period r := by
  simp only [ContinuousPhasePath.pos, biPeriodicPos, hd]
  exact lift_add_scale hv _ _

theorem path_stableTime_eq {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (r : Nat) :
    stableTime v P w (p.phase r) =
      p.period r * (P : Int) + (p.phase r : Int) - (P : Int) * lift v (p.pos w r) := by
  rw [path_lift_pos p hd hv r, Int.mul_add, Int.mul_comm (P : Int) (p.period r)]
  unfold stableTime
  omega

/-- Seam-corrected stable-time difference along any continuous path whose endpoints differ by `δ•v`. -/
theorem path_stableTime_difference {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) {δ : Int}
    (hdisp : p.pos w len = addPoint (p.pos w 0) (scalePoint v δ)) :
    stableTime v P w (p.phase len) - stableTime v P w (p.phase 0) =
      (len : Int) - (P : Int) * δ := by
  have hlift : lift v (p.pos w len) = lift v (p.pos w 0) + δ := by
    rw [hdisp]
    exact lift_add_scale hv (p.pos w 0) δ
  rw [path_stableTime_eq p hd hv len, path_stableTime_eq p hd hv 0, hlift, Int.mul_add]
  have ht := p.time_eq (Nat.le_refl len)
  omega

theorem path_stableTime_difference_of_sameClass {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hsc : SameClass v (p.pos w 0) (p.pos w len)) :
    stableTime v P w (p.phase len) - stableTime v P w (p.phase 0) =
      (len : Int) - (P : Int) * (lift v (p.pos w len) - lift v (p.pos w 0)) :=
  path_stableTime_difference p hd hv (sameClass_eq_add_scale hsc)

theorem path_return_stableTime {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hret : p.pos w len = p.pos w 0) :
    stableTime v P w (p.phase len) = stableTime v P w (p.phase 0) + (len : Int) := by
  have hh := path_stableTime_difference p hd hv (δ := 0) (by simpa [scalePoint_zero] using hret)
  omega

theorem path_return_phase_ne {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hlen : 0 < len) (hret : p.pos w len = p.pos w 0) :
    p.phase len ≠ p.phase 0 := by
  intro he
  have := path_return_stableTime p hd hv hret
  rw [he] at this
  omega

/-- Completeness of stable-time visits inside a continuous path for arbitrary drift. -/
theorem path_visit_of_stableTime {v : Point} {P len j r : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v)
    (hj : j < P) (hr : r ≤ len)
    (hsc : SameClass v (wordPos w j) (wordPos w (p.phase 0)))
    (ht : stableTime v P w j = stableTime v P w (p.phase 0) + (r : Int)) :
    p.pos w r = p.pos w 0 := by
  let k : Int := p.period 0 + (lift v (wordPos w (p.phase 0)) - lift v (wordPos w j))
  have htime : k * (P : Int) + (j : Int) = p.period r * (P : Int) + (p.phase r : Int) := by
    dsimp [k]
    rw [Int.add_mul, Int.sub_mul, Int.mul_comm (lift v (wordPos w (p.phase 0))),
      Int.mul_comm (lift v (wordPos w j))]
    have := p.time_eq hr
    unfold stableTime at ht
    omega
  have he := biTime_injective hj (p.phase_lt r hr) htime
  change biPeriodicPos P w (p.period r) (p.phase r) = _
  rw [← he.1, ← he.2]
  simp only [ContinuousPhasePath.pos, biPeriodicPos, hd]
  have hshift := sameClass_eq_add_scale hsc
  have hcomb := addPoint_scalePoint_add v (wordPos w j)
    (lift v (wordPos w (p.phase 0)) - lift v (wordPos w j)) (p.period 0)
  rw [← hshift] at hcomb
  have hkcomm : k = (lift v (wordPos w (p.phase 0)) - lift v (wordPos w j)) + p.period 0 := by
    dsimp [k]; omega
  rw [hkcomm, ← hcomb]

/-- A first physical return advances stable rank by exactly one, for arbitrary nonzero drift. -/
theorem path_firstReturn_rank {v : Point} {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hlen : 0 < len) (hret : p.pos w len = p.pos w 0)
    (hfirst : ∀ r, 0 < r → r < len → p.pos w r ≠ p.pos w 0) :
    stableRank P w (p.phase len) = stableRank P w (p.phase 0) + 1 := by
  have hkey := path_return_stableTime p hd hv hret
  have hsc : SameClass v (wordPos w (p.phase 0)) (wordPos w (p.phase len)) := by
    have h0 := path_sameClass_pos p hd 0
    have hl := path_sameClass_pos p hd len
    rw [hret] at hl
    exact h0.trans hl.symm
  apply (stableRank_succ_iff hd hv (p.phase_lt 0 (by omega))
    (p.phase_lt len (by omega)) hsc).mpr
  refine ⟨by omega, ?_⟩
  rintro ⟨j, hj, hjc, ht0, htlen⟩
  let r := (stableTime v P w j - stableTime v P w (p.phase 0)).toNat
  have hr : (r : Int) = stableTime v P w j - stableTime v P w (p.phase 0) := by
    dsimp [r]
    omega
  exact hfirst r (by omega) (by omega)
    (path_visit_of_stableTime p hd hj (by omega) hjc (by omega))

/-! ## 4. Ordered matching between translation classes -/

abbrev inDir := UnitDiagonalMatching.inDir
abbrev outDir := UnitDiagonalMatching.outDir
abbrev succ := UnitDiagonalMatching.succ
abbrev pred := UnitDiagonalMatching.pred

/-- Canonical target basepoint reached by stepping in direction `d` from class `c`. -/
def targetClass (v c : Point) (d : Direction) : Point :=
  base v (move (base v c) d)

/-- Constant change in `lift v` when stepping in direction `d` from any point in class `c`. -/
def liftStep (v c : Point) (d : Direction) : Int :=
  lift v (move (base v c) d)

theorem targetClass_congr {v c₁ c₂ : Point} (h : SameClass v c₁ c₂) (d : Direction) :
    targetClass v c₁ d = targetClass v c₂ d := by
  simp [targetClass, (sameClass_iff_base_eq v c₁ c₂).mp h]

theorem liftStep_congr {v c₁ c₂ : Point} (h : SameClass v c₁ c₂) (d : Direction) :
    liftStep v c₁ d = liftStep v c₂ d := by
  simp [liftStep, (sameClass_iff_base_eq v c₁ c₂).mp h]

theorem sameClass_targetClass (v c : Point) (d : Direction) :
    SameClass v (targetClass v c d) (move c d) :=
  (sameClass_base v (move (base v c) d)).trans
    ((sameClass_move_iff v (base v c) c d).mpr (sameClass_base v c))

/-- Basepoint transition identity generalizing `UnitDiagonalMatching.basepoint_move`. -/
theorem basepoint_move (v c : Point) (d : Direction) :
    move (base v c) d =
      addPoint (targetClass v c d) (scalePoint v (liftStep v c d)) :=
  decomp v (move (base v c) d)

theorem lift_move {v : Point} (hv : v ≠ (0, 0)) (p : Point) (d : Direction) :
    lift v (move p d) = lift v p + liftStep v p d := by
  have hp : move p d = addPoint (move (base v p) d) (scalePoint v (lift v p)) := by
    rw [← move_addPoint_right, ← decomp v p]
  rw [hp, lift_add_scale hv]
  unfold liftStep
  omega

theorem lift_move_of_sameClass {v p c : Point} (hv : v ≠ (0, 0))
    (h : SameClass v p c) (d : Direction) :
    lift v (move p d) = lift v p + liftStep v c d := by
  rw [lift_move hv p d, liftStep_congr h d]

theorem successor_class {v : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hi : i < P) :
    SameClass v (wordPos w (succ P i)) (move (wordPos w i) (outDir w i)) := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i 1
  have h0 : p.phase 0 = i := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have h1 : p.phase 1 = succ P i := rfl
  have hs := p.pos_step (w := w) (r := 0) (by omega)
  have hp0 : SameClass v (p.pos w 0) (wordPos w i) := by
    simpa only [h0] using (path_sameClass_pos p hd 0).symm
  have hp1 : SameClass v (wordPos w (succ P i)) (p.pos w 1) := by
    simpa only [h1] using path_sameClass_pos p hd 1
  rw [hs, h0] at hp1
  exact hp1.trans ((sameClass_move_iff v (p.pos w 0) (wordPos w i) (outDir w i)).mpr hp0)

/-- The seam carry cancels out of stable time, leaving a constant shift depending only on
the source class and outgoing direction. -/
theorem successor_stableTime {v : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    stableTime v P w (succ P i) =
      stableTime v P w i + 1 - (P : Int) * liftStep v (wordPos w i) (outDir w i) := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i 1
  have h0 : p.phase 0 = i := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have h1 : p.phase 1 = succ P i := rfl
  have ht := p.time_step 0 (by omega)
  have hs := p.pos_step (w := w) (r := 0) (by omega)
  have hp0 : SameClass v (p.pos w 0) (wordPos w i) := by
    simpa only [h0] using (path_sameClass_pos p hd 0).symm
  have hlift : lift v (p.pos w 1) = lift v (p.pos w 0) + liftStep v (wordPos w i) (outDir w i) := by
    rw [hs, h0]
    exact lift_move_of_sameClass hv hp0 (outDir w i)
  have t0 := path_stableTime_eq p hd hv 0
  have t1 := path_stableTime_eq p hd hv 1
  rw [hlift, Int.mul_add] at t1
  simp only [h0, h1, Nat.zero_add] at ht t0 t1
  omega

theorem successor_stableTime_of_class {v c : Point} {P i : Nat} {w : Nat → Bool} {d : Direction}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i < P) (hc : SameClass v (wordPos w i) c) (ho : outDir w i = d) :
    stableTime v P w (succ P i) =
      stableTime v P w i + 1 - (P : Int) * liftStep v c d := by
  rw [successor_stableTime hd hv hi, ho, liftStep_congr hc d]

def departures (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (d : Direction) : List Nat :=
  (classPhases v P w c).filter (fun i => decide (outDir w i = d))

def arrivals (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (d : Direction) : List Nat :=
  (classPhases v P w c).filter (fun i => decide (inDir w i = d))

theorem mem_departures {v c : Point} {P i : Nat} {w : Nat → Bool} {d : Direction} :
    i ∈ departures v P w c d ↔ i < P ∧ SameClass v (wordPos w i) c ∧ outDir w i = d := by
  simp [departures, mem_classPhases, and_assoc]

theorem mem_arrivals {v c : Point} {P i : Nat} {w : Nat → Bool} {d : Direction} :
    i ∈ arrivals v P w c d ↔ i < P ∧ SameClass v (wordPos w i) c ∧ inDir w i = d := by
  simp [arrivals, mem_classPhases, and_assoc]

theorem departures_nodup (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (d : Direction) :
    (departures v P w c d).Nodup :=
  (classPhases_nodup v P w c).filter _

theorem arrivals_nodup (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (d : Direction) :
    (arrivals v P w c d).Nodup :=
  (classPhases_nodup v P w c).filter _

theorem departures_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool) (d : Direction)
    (h : SameClass v c₁ c₂) :
    departures v P w c₁ d = departures v P w c₂ d := by
  simp [departures, classPhases_congr P w h]

theorem arrivals_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool) (d : Direction)
    (h : SameClass v c₁ c₂) :
    arrivals v P w c₁ d = arrivals v P w c₂ d := by
  simp [arrivals, classPhases_congr P w h]

theorem arrivals_targetClass (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (d : Direction) :
    arrivals v P w (targetClass v c d) d = arrivals v P w (move c d) d :=
  arrivals_congr P w d (sameClass_targetClass v c d)

theorem successor_heading {P i : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hi : i < P) :
    inDir w (succ P i) = outDir w i :=
  UnitDiagonalMatching.successor_heading hh hi

theorem successor_mem_iff {v c : Point} {P i : Nat} {w : Nat → Bool} {d : Direction}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = v) (hi : i < P) :
    succ P i ∈ arrivals v P w (move c d) d ↔ i ∈ departures v P w c d := by
  rw [mem_arrivals, mem_departures, successor_heading hh hi]
  have hsc := successor_class hd hi
  constructor
  · rintro ⟨_, hcls, ho⟩
    rw [ho] at hsc
    have hm : SameClass v (move (wordPos w i) d) (move c d) := hsc.symm.trans hcls
    exact ⟨hi, (sameClass_move_iff v (wordPos w i) c d).mp hm, ho⟩
  · rintro ⟨_, hcls, ho⟩
    rw [ho] at hsc
    have hm : SameClass v (move (wordPos w i) d) (move c d) :=
      (sameClass_move_iff v (wordPos w i) c d).mpr hcls
    exact ⟨UnitDiagonalMatching.succ_lt (by omega), hsc.trans hm, ho⟩

theorem successor_target_sameClass {v c : Point} {P i : Nat} {w : Nat → Bool} {d : Direction}
    (hd : wordDrift P w = v) (hi : i ∈ departures v P w c d) :
    SameClass v (move c d) (wordPos w (succ P i)) := by
  obtain ⟨hiP, hic, hid⟩ := mem_departures.mp hi
  have h1 := successor_class hd hiP
  rw [hid] at h1
  exact ((sameClass_move_iff v c (wordPos w i) d).mpr hic.symm).trans h1.symm

theorem predecessor_mem {v c : Point} {P j : Nat} {w : Nat → Bool} {d : Direction}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = v)
    (hj : j ∈ arrivals v P w (move c d) d) :
    pred P j ∈ departures v P w c d := by
  have hjP := (mem_arrivals.mp hj).1
  apply (successor_mem_iff hh hd (UnitDiagonalMatching.pred_lt hjP)).mp
  simpa only [UnitDiagonalMatching.succ_pred hjP] using hj

/-- Successor maps departures from class `c` in direction `d` bijectively onto arrivals at
the target class `move c d` in direction `d`, with cyclic predecessor as its inverse. -/
theorem successor_bijection {v : Point} {P : Nat} {w : Nat → Bool} (c : Point) (d : Direction)
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = v) :
    (∀ i ∈ departures v P w c d,
      succ P i ∈ arrivals v P w (move c d) d ∧ pred P (succ P i) = i) ∧
    (∀ j ∈ arrivals v P w (move c d) d,
      pred P j ∈ departures v P w c d ∧ succ P (pred P j) = j) := by
  constructor
  · intro i hi
    have hiP := (mem_departures.mp hi).1
    exact ⟨(successor_mem_iff hh hd hiP).mpr hi, UnitDiagonalMatching.pred_succ hiP⟩
  · intro j hj
    exact ⟨predecessor_mem hh hd hj, UnitDiagonalMatching.succ_pred (mem_arrivals.mp hj).1⟩

theorem successor_onto {v c : Point} {P : Nat} {w : Nat → Bool} {d : Direction}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = v) (j : Nat) :
    j ∈ arrivals v P w (move c d) d ↔ ∃ i ∈ departures v P w c d, succ P i = j := by
  constructor
  · intro hj
    exact ⟨pred P j, predecessor_mem hh hd hj, UnitDiagonalMatching.succ_pred (mem_arrivals.mp hj).1⟩
  · rintro ⟨i, hi, rfl⟩
    exact (successor_mem_iff hh hd (mem_departures.mp hi).1).mpr hi

theorem departures_length_eq_arrivals_length {v c : Point} {P : Nat} {w : Nat → Bool}
    {d : Direction} (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = v) :
    (departures v P w c d).length = (arrivals v P w (move c d) d).length := by
  have hp : ((departures v P w c d).map (succ P)).Perm (arrivals v P w (move c d) d) := by
    apply (List.perm_ext_iff_of_nodup
      (nodup_map_on (departures_nodup v P w c d)
        (fun _ hj _ hk =>
          UnitDiagonalMatching.succ_injective (mem_departures.mp hj).1 (mem_departures.mp hk).1))
      (arrivals_nodup v P w (move c d) d)).mpr
    intro j
    simpa only [List.mem_map] using (successor_onto hh hd j).symm
  simpa only [List.length_map] using hp.length_eq

theorem successor_stableTime_order {v c : Point} {P i j : Nat} {w : Nat → Bool} {d : Direction}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ departures v P w c d) (hj : j ∈ departures v P w c d) :
    stableTime v P w i < stableTime v P w j ↔
      stableTime v P w (succ P i) < stableTime v P w (succ P j) := by
  obtain ⟨hiP, hic, hid⟩ := mem_departures.mp hi
  obtain ⟨hjP, hjc, hjd⟩ := mem_departures.mp hj
  rw [successor_stableTime_of_class hd hv hiP hic hid,
    successor_stableTime_of_class hd hv hjP hjc hjd]
  omega

/-- The zero-based position in the departure stable-time order equals the arrival position. -/
theorem departure_position_eq_arrival_position {v c : Point} {P i : Nat} {w : Nat → Bool}
    {d : Direction} (hh : (wordTrace w P).2 = .north)
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ departures v P w c d) :
    ((departures v P w c d).filter
        (fun j => decide (stableTime v P w j < stableTime v P w i))).length =
    ((arrivals v P w (move c d) d).filter
        (fun j => decide (stableTime v P w j < stableTime v P w (succ P i)))).length := by
  exact ordered_bijection_position _ _ (succ P)
    (fun j k => stableTime v P w j < stableTime v P w k)
    (fun j k => stableTime v P w j < stableTime v P w k)
    (departures_nodup v P w c d) (arrivals_nodup v P w (move c d) d)
    (fun _ hj _ hk =>
      UnitDiagonalMatching.succ_injective (mem_departures.mp hj).1 (mem_departures.mp hk).1)
    (successor_onto hh hd)
    (fun _ hj _ hk => successor_stableTime_order hd hv hj hk) hi

/-- Variant naming the target class by any representative `c'` (such as `wordPos w (succ P i)`
or `targetClass v c d`). -/
theorem departure_position_eq_arrival_position_of_target {v c c' : Point} {P i : Nat}
    {w : Nat → Bool} {d : Direction} (hh : (wordTrace w P).2 = .north)
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : SameClass v (move c d) c') (hi : i ∈ departures v P w c d) :
    ((departures v P w c d).filter
        (fun j => decide (stableTime v P w j < stableTime v P w i))).length =
    ((arrivals v P w c' d).filter
        (fun j => decide (stableTime v P w j < stableTime v P w (succ P i)))).length := by
  rw [← arrivals_congr P w d ht]
  exact departure_position_eq_arrival_position hh hd hv hi

/-- The same directed matching is strictly increasing when events are ordered by `stableRank`. -/
theorem successor_rank_order {v c : Point} {P i j : Nat} {w : Nat → Bool} {d : Direction}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ departures v P w c d) (hj : j ∈ departures v P w c d) :
    stableRank P w i < stableRank P w j ↔
      stableRank P w (succ P i) < stableRank P w (succ P j) := by
  obtain ⟨hiP, hic, hid⟩ := mem_departures.mp hi
  obtain ⟨hjP, hjc, hjd⟩ := mem_departures.mp hj
  have hsi : SameClass v (wordPos w (succ P i)) (move c d) := by
    have h1 := successor_class hd hiP
    rw [hid] at h1
    exact h1.trans ((sameClass_move_iff v (wordPos w i) c d).mpr hic)
  have hsj : SameClass v (wordPos w (succ P j)) (move c d) := by
    have h1 := successor_class hd hjP
    rw [hjd] at h1
    exact h1.trans ((sameClass_move_iff v (wordPos w j) c d).mpr hjc)
  rw [stableRank_lt_iff_stableTime_lt hd hv hiP hjP (hic.trans hjc.symm),
    stableRank_lt_iff_stableTime_lt hd hv
      (UnitDiagonalMatching.succ_lt (by omega))
      (UnitDiagonalMatching.succ_lt (by omega))
      (hsi.trans hsj.symm)]
  exact successor_stableTime_order hd hv hi hj

theorem departure_rank_position_eq_arrival_rank_position {v c : Point} {P i : Nat}
    {w : Nat → Bool} {d : Direction} (hh : (wordTrace w P).2 = .north)
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ departures v P w c d) :
    ((departures v P w c d).filter
        (fun j => decide (stableRank P w j < stableRank P w i))).length =
    ((arrivals v P w (move c d) d).filter
        (fun j => decide (stableRank P w j < stableRank P w (succ P i)))).length := by
  exact ordered_bijection_position _ _ (succ P)
    (fun j k => stableRank P w j < stableRank P w k)
    (fun j k => stableRank P w j < stableRank P w k)
    (departures_nodup v P w c d) (arrivals_nodup v P w (move c d) d)
    (fun _ hj _ hk =>
      UnitDiagonalMatching.succ_injective (mem_departures.mp hj).1 (mem_departures.mp hk).1)
    (successor_onto hh hd)
    (fun _ hj _ hk => successor_rank_order hd hv hj hk) hi

theorem departure_rank_position_eq_arrival_rank_position_of_target {v c c' : Point} {P i : Nat}
    {w : Nat → Bool} {d : Direction} (hh : (wordTrace w P).2 = .north)
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : SameClass v (move c d) c') (hi : i ∈ departures v P w c d) :
    ((departures v P w c d).filter
        (fun j => decide (stableRank P w j < stableRank P w i))).length =
    ((arrivals v P w c' d).filter
        (fun j => decide (stableRank P w j < stableRank P w (succ P i)))).length := by
  rw [← arrivals_congr P w d ht]
  exact departure_rank_position_eq_arrival_rank_position hh hd hv hi

/-! ## 5. Consistency with `UnitDiagonalRank` and non-vacuity on the standard highway -/

theorem unitDiagonal_lift (p : Point) :
    lift (1, -1) p = LangtonsAnt.lift p := by
  simp [lift, LangtonsAnt.lift, Int.ediv_one]

theorem unitDiagonal_base (p : Point) :
    base (1, -1) p = (0, weight p) := by
  apply Prod.ext <;>
    simp [base, unitDiagonal_lift, LangtonsAnt.lift, addPoint, scalePoint, weight] <;> omega

theorem unitDiagonal_sameClass_iff_weight (p q : Point) :
    SameClass (1, -1) p q ↔ weight p = weight q := by
  rw [sameClass_iff_base_eq, unitDiagonal_base, unitDiagonal_base]
  simp

theorem unitDiagonal_sameClass_iff_layer (p q : Point) :
    SameClass (1, -1) p q ↔ layer p = layer q :=
  unitDiagonal_sameClass_iff_weight p q

theorem unitDiagonal_stableTime (P : Nat) (w : Nat → Bool) (i : Nat) :
    stableTime (1, -1) P w i = LangtonsAnt.stableTime P w i := by
  simp [stableTime, LangtonsAnt.stableTime, unitDiagonal_lift, LangtonsAnt.lift]

theorem stableRank_eq_unitDiagonal (P : Nat) (w : Nat → Bool) (i : Nat) :
    stableRank P w i = LangtonsAnt.stableRank P w i :=
  rfl

theorem unitDiagonal_classPhases (P : Nat) (w : Nat → Bool) (c : Point) :
    classPhases (1, -1) P w c = layerPhases P w (layer c) := by
  unfold classPhases layerPhases
  apply List.filter_congr
  intro i _
  exact Bool.eq_iff_iff.mpr (by simp [unitDiagonal_sameClass_iff_layer])

theorem unitDiagonal_liftStep (c : Point) (d : Direction) :
    liftStep (1, -1) c d = UnitDiagonalMatching.delta d := by
  unfold liftStep
  rw [unitDiagonal_lift, unitDiagonal_base]
  cases d <;> simp [LangtonsAnt.lift, move, UnitDiagonalMatching.delta]

/-- The standard 104-step highway word has full period drift `(-2, -2)`. -/
theorem standard_word_drift : wordDrift 104 certifiedColor = (-2, -2) := by
  have hr : readColor highwaySeed.toState = certifiedColor :=
    funext highwaySeed_exact_reads
  rw [← hr]
  exact highwaySeed_highway.word_drift rfl rfl

/-- Non-vacuity: the standard 104-step highway (`P = 104`, drift `(-2, -2)`) satisfies all
hypotheses of the general drift-rank and ordered-matching toolkit. -/
theorem standard_word_nonvacuous :
    ConsistentWord 104 certifiedColor ∧
    wordDrift 104 certifiedColor = (-2, -2) ∧
    ((-2 : Int), (-2 : Int)) ≠ (0, 0) ∧
    (∀ i j, i < 104 →
      (j ∈ priorPhases 104 certifiedColor i ↔
        j < 104 ∧
        SameClass (-2, -2) (wordPos certifiedColor j) (wordPos certifiedColor i) ∧
        stableTime (-2, -2) 104 certifiedColor j <
          stableTime (-2, -2) 104 certifiedColor i)) := by
  have hv : ((-2 : Int), (-2 : Int)) ≠ (0, 0) := by decide
  refine ⟨standard_word_consistent, standard_word_drift, hv, ?_⟩
  intro i j hi
  exact mem_priorPhases_iff_stableTime standard_word_drift hv hi

/-- For drift `(-2, -2)`, points on the same transverse line `x - y = 0` can belong to
distinct full-translation classes (`gcd(|-2|, |-2|) = 2` classes per transverse layer). -/
theorem standard_drift_splits_layer :
    ¬ SameClass (-2, -2) (0, 0) (1, 1) := by
  decide

end Drift
end LangtonsAnt
