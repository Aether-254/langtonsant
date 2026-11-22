import PeriodicGrowthResidue
import UnitDiagonalExtremal

/-!
# Transverse extremal-line rigidity and pure-odd-layer flux cancellation for drift `(2, -2)`

This module formalizes blueprint items **L21** (Jillhewar Thm 9.1 instantiated at full drift
`(2, -2)`, proved first for arbitrary anti-diagonal drift `layer (wordDrift P w) = 0`) and
**L22** (exact two-lane flow conservation, pure-odd-layer flux cancellation, local mod-4
turn-count congruences, and vanishing of the local non-inversion correction `L ≡ 0 (mod 2)`),
purely in the Lean kernel (no `sorry`, no `axiom`, no `native_decide`).

## Naming conventions

To avoid name clashes between `LangtonsAnt.Drift.*` and `UnitDiagonal*`, we work inside
`LangtonsAnt.TwoCellDiagonal` and always qualify `Drift.*` declarations explicitly.
-/

namespace LangtonsAnt
namespace TwoCellDiagonal

/-! ## 1. Two-cell diagonal coordinates `(layer, lane)` for drift `(2, -2)` -/

/-- The `x mod 2` lane of a grid point: `false` for even `x`, `true` for odd `x`. -/
def lane (p : Point) : Bool :=
  decide (p.1 % 2 = 1)

/-- Canonical representative of the `(2, -2)` translation class at layer `t = x + y` and lane `r`. -/
def classRep (t : Int) (r : Bool) : Point :=
  if r then (1, t - 1) else (0, t)

/-- Phases in `[0, P)` belonging to the `(2, -2)` translation class `(t, r)`. -/
def classPhases2 (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : List Nat :=
  Drift.classPhases (2, -2) P w (classRep t r)

/-- Visit multiplicity of the `(2, -2)` translation class `(t, r)` over one period. -/
def classMult (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat :=
  (classPhases2 P w t r).length

theorem drift_two_negTwo_ne_zero : ((2 : Int), (-2 : Int)) ≠ (0, 0) := by
  decide

theorem layer_two_negTwo : layer (2, -2) = 0 := by
  decide

theorem layer_eq_add (p : Point) : layer p = p.1 + p.2 :=
  rfl

theorem layer_classRep (t : Int) (r : Bool) : layer (classRep t r) = t := by
  cases r <;> simp [classRep, layer, weight] <;> omega

theorem lane_classRep (t : Int) (r : Bool) : lane (classRep t r) = r := by
  cases r <;> simp [classRep, lane]

theorem lane_eq_false_iff (p : Point) : lane p = false ↔ p.1 % 2 = 0 := by
  unfold lane
  simp only [decide_eq_false_iff_not]
  omega

theorem lane_eq_true_iff (p : Point) : lane p = true ↔ p.1 % 2 = 1 := by
  simp [lane]

theorem layer_addPoint (p q : Point) : layer (addPoint p q) = layer p + layer q := by
  simp only [layer, weight, addPoint]
  omega

theorem layer_scalePoint (v : Point) (k : Int) : layer (scalePoint v k) = k * layer v := by
  simp only [layer, weight, scalePoint, Int.mul_add]

theorem layer_eq_of_sameClass {v p q : Point} (hv : layer v = 0) (h : Drift.SameClass v p q) :
    layer p = layer q := by
  obtain ⟨k, rfl⟩ := h
  rw [layer_addPoint, layer_scalePoint, hv]
  omega

theorem base_two_negTwo (p : Point) :
    Drift.base (2, -2) p = classRep (layer p) (lane p) := by
  unfold Drift.base Drift.lift classRep lane layer weight addPoint scalePoint
  by_cases h1 : p.1 % 2 = 1
  · simp only [show (2 : Int) ≠ 0 by decide, ite_false, h1, decide_true, ite_true]
    apply Prod.ext <;> omega
  · simp only [show (2 : Int) ≠ 0 by decide, ite_false, h1, decide_false, Bool.false_eq_true,
      ite_false]
    apply Prod.ext <;> omega

theorem sameClass_two_negTwo_iff (p q : Point) :
    Drift.SameClass (2, -2) p q ↔ layer p = layer q ∧ lane p = lane q := by
  rw [Drift.sameClass_iff_base_eq, base_two_negTwo, base_two_negTwo]
  constructor
  · intro h
    have hlayer := congrArg layer h
    have hlane := congrArg lane h
    rw [layer_classRep, layer_classRep] at hlayer
    rw [lane_classRep, lane_classRep] at hlane
    exact ⟨hlayer, hlane⟩
  · rintro ⟨hl, hr⟩
    rw [hl, hr]

theorem sameClass_two_negTwo_classRep (p : Point) (t : Int) (r : Bool) :
    Drift.SameClass (2, -2) p (classRep t r) ↔ layer p = t ∧ lane p = r := by
  rw [sameClass_two_negTwo_iff, layer_classRep, lane_classRep]

theorem mem_classPhases2 {P i : Nat} {w : Nat → Bool} {t : Int} {r : Bool} :
    i ∈ classPhases2 P w t r ↔ i < P ∧ layer (wordPos w i) = t ∧ lane (wordPos w i) = r := by
  simp [classPhases2, Drift.mem_classPhases, sameClass_two_negTwo_classRep]

theorem classPhases2_nodup (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) :
    (classPhases2 P w t r).Nodup :=
  Drift.classPhases_nodup (2, -2) P w (classRep t r)

theorem sameClass_move_classRep_north (t : Int) (r : Bool) :
    Drift.SameClass (2, -2) (move (classRep t r) .north) (classRep (t + 1) r) := by
  rw [sameClass_two_negTwo_classRep]
  cases r <;> simp [classRep, move, layer, weight, lane] <;> omega

theorem sameClass_move_classRep_south (t : Int) (r : Bool) :
    Drift.SameClass (2, -2) (move (classRep t r) .south) (classRep (t - 1) r) := by
  rw [sameClass_two_negTwo_classRep]
  cases r <;> simp [classRep, move, layer, weight, lane] <;> omega

theorem sameClass_move_classRep_east (t : Int) (r : Bool) :
    Drift.SameClass (2, -2) (move (classRep t r) .east) (classRep (t + 1) (!r)) := by
  rw [sameClass_two_negTwo_classRep]
  cases r <;> simp [classRep, move, layer, weight, lane] <;> omega

theorem sameClass_move_classRep_west (t : Int) (r : Bool) :
    Drift.SameClass (2, -2) (move (classRep t r) .west) (classRep (t - 1) (!r)) := by
  rw [sameClass_two_negTwo_classRep]
  cases r <;> simp [classRep, move, layer, weight, lane] <;> omega

theorem checkerSign_eq_of_layer (p : Point) :
    checkerSign p = if layer p % 2 = 0 then 1 else -1 :=
  rfl

theorem checkerSign_eq_one_iff_layer_even (p : Point) :
    checkerSign p = 1 ↔ layer p % 2 = 0 := by
  rw [checkerSign_eq_of_layer]
  split <;> omega

theorem checkerSign_eq_neg_one_iff_layer_odd (p : Point) :
    checkerSign p = -1 ↔ layer p % 2 = 1 := by
  rw [checkerSign_eq_of_layer]
  split <;> omega

private theorem filter_length_add_not' {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx] <;> omega

/-- Every transverse layer `L` splits disjointly into the two `(2, -2)` lanes `false` and `true`. -/
theorem layerPhases_length_eq_add_classMult (P : Nat) (w : Nat → Bool) (L : Int) :
    (layerPhases P w L).length = classMult P w L false + classMult P w L true := by
  have hF : classPhases2 P w L false =
      (layerPhases P w L).filter (fun i => !(lane (wordPos w i))) := by
    unfold classPhases2 Drift.classPhases layerPhases
    rw [List.filter_filter]
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      sameClass_two_negTwo_classRep, and_comm]
  have hT : classPhases2 P w L true =
      (layerPhases P w L).filter (fun i => lane (wordPos w i)) := by
    unfold classPhases2 Drift.classPhases layerPhases
    rw [List.filter_filter]
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true, sameClass_two_negTwo_classRep, and_comm]
  unfold classMult
  rw [hF, hT]
  have hsum := filter_length_add_not' (fun i => lane (wordPos w i)) (layerPhases P w L)
  omega

/-! ## 2. General anti-diagonal extremal-line rigidity (Jillhewar Thm 9.1) and L21 for `(2, -2)` -/

private theorem list_eq_singleton_of_nodup' {α : Type} {l : List α} {a : α}
    (hnd : l.Nodup) (ha : a ∈ l) (huniq : ∀ b, b ∈ l → b = a) : l = [a] := by
  cases l with
  | nil => simp at ha
  | cons x xs =>
    have hx : x = a := huniq x (by simp)
    subst hx
    have hxs : xs = [] := by
      cases xs with
      | nil => rfl
      | cons y ys =>
        have hy : y = x := huniq y (by simp)
        subst hy
        have hnot := (List.nodup_cons.mp hnd).1
        simp at hnot
    rw [hxs]

theorem layer_wordPos_nextPhase_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (hlv : layer (wordDrift P w) = 0) (hi : i < P) :
    layer (wordPos w (nextPhase P i)) = layer (wordPos w i) + layerDelta (outDir w i) := by
  rw [nextPhase_eq_ite hi]
  split
  · exact layer_wordPos_succ w i
  · rename_i hge
    have heq : i + 1 = P := by omega
    have hstep := layer_wordPos_succ w i
    rw [heq] at hstep
    have hP0 : layer (wordPos w P) = layer (wordPos w 0) := by
      change layer (wordDrift P w) = layer (wordPos w 0)
      rw [hlv]
      simp [layer, weight, wordPos, wordTrace]
    omega

theorem layer_wordPos_prevPhase_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (hi : i < P) :
    layer (wordPos w i) = layer (wordPos w (prevPhase P i)) + layerDelta (inDir w i) := by
  have h := layer_wordPos_nextPhase_of_layer_zero hlv (prevPhase_lt hi)
  rw [nextPhase_prevPhase hi, outDir_prevPhase hdir hi] at h
  exact h

private theorem topLayer_forced_turn_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (hi : i < P)
    (htop : layer (wordPos w i) = topLayer P w) :
    w i = !(inDir w i).horizontal ∧ layerDelta (inDir w i) = 1 ∧ layerDelta (outDir w i) = -1 := by
  have hprev := layer_wordPos_prevPhase_of_layer_zero h.1 hlv hi
  have hprev_le : layer (wordPos w (prevPhase P i)) ≤ topLayer P w :=
    layer_le_topLayer (prevPhase_lt hi)
  have hnext := layer_wordPos_nextPhase_of_layer_zero hlv hi
  have hnext_le : layer (wordPos w (nextPhase P i)) ≤ topLayer P w :=
    layer_le_topLayer (nextPhase_lt h.pos_period)
  have hin : layerDelta (inDir w i) = 1 := by
    rcases layerDelta_unit (inDir w i) with h1 | h1 <;> omega
  have hout : layerDelta (outDir w i) = -1 := by
    rcases layerDelta_unit (outDir w i) with h1 | h1 <;> omega
  refine ⟨?_, hin, hout⟩
  unfold outDir at hout
  cases hd' : inDir w i <;> cases hw : w i <;>
    simp [hd', hw, turn, Direction.left, Direction.right, Direction.horizontal, layerDelta] at hin hout ⊢

private theorem botLayer_forced_turn_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (hi : i < P)
    (hbot : layer (wordPos w i) = botLayer P w) :
    w i = !(inDir w i).horizontal ∧ layerDelta (inDir w i) = -1 ∧ layerDelta (outDir w i) = 1 := by
  have hprev := layer_wordPos_prevPhase_of_layer_zero h.1 hlv hi
  have hprev_ge : botLayer P w ≤ layer (wordPos w (prevPhase P i)) :=
    botLayer_le_layer (prevPhase_lt hi)
  have hnext := layer_wordPos_nextPhase_of_layer_zero hlv hi
  have hnext_ge : botLayer P w ≤ layer (wordPos w (nextPhase P i)) :=
    botLayer_le_layer (nextPhase_lt h.pos_period)
  have hin : layerDelta (inDir w i) = -1 := by
    rcases layerDelta_unit (inDir w i) with h1 | h1 <;> omega
  have hout : layerDelta (outDir w i) = 1 := by
    rcases layerDelta_unit (outDir w i) with h1 | h1 <;> omega
  refine ⟨?_, hin, hout⟩
  unfold outDir at hout
  cases hd' : inDir w i <;> cases hw : w i <;>
    simp [hd', hw, turn, Direction.left, Direction.right, Direction.horizontal, layerDelta] at hin hout ⊢

/-- **Jillhewar Theorem 9.1 (top extremal line, arbitrary anti-diagonal drift `layer v = 0`):**
Every phase `i < P` attaining `topLayer P w` is the unique visit in its full translation class,
has `stableRank = 0`, reads white (`false`), arrives `.east`, leaves `.south`, belongs to
`oddClassReps P w`, and carries checkerboard sign `χ = -1` (horizontal / odd layer). -/
theorem topLayer_phase_rigid_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0)
    (hi : i < P) (htop : layer (wordPos w i) = topLayer P w) :
    Drift.stableRank P w i = 0 ∧
    w i = false ∧
    inDir w i = .east ∧
    outDir w i = .south ∧
    sameClassPhases P w i = [i] ∧
    (sameClassPhases P w i).length = 1 ∧
    (∀ j, j < P → Drift.SameClass (wordDrift P w) (wordPos w j) (wordPos w i) → j = i) ∧
    i ∈ oddClassReps P w ∧
    checkerSign (wordPos w i) = -1 := by
  let C := sameClassPhases P w i
  have hiC : i ∈ C := Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩
  have hCpos : 0 < C.length := List.length_pos_of_mem hiC
  obtain ⟨r0, hr0C, hr0rank⟩ :=
    Drift.stableRank_surjective_on_class (v := wordDrift P w) (c := wordPos w i) rfl h.2.1 hCpos
  obtain ⟨hr0P, hr0sc⟩ := Drift.mem_classPhases.mp hr0C
  have hr0top : layer (wordPos w r0) = topLayer P w :=
    (layer_eq_of_sameClass hlv hr0sc).trans htop
  have hwr0 : w r0 = false := by
    rw [Drift.consistentWord_stableRank_color h hr0P, hr0rank]
    rfl
  obtain ⟨hcol0, hin0, _⟩ := topLayer_forced_turn_of_layer_zero h hlv hr0P hr0top
  have hdir_in0 : inDir w r0 = .east := by
    cases hd' : inDir w r0 <;>
      simp [hd', hwr0, Direction.horizontal, layerDelta] at hcol0 hin0 ⊢
  have hClen_le : C.length ≤ 1 := by
    by_cases hle : C.length ≤ 1
    · exact hle
    · exfalso
      have h1lt : 1 < C.length := by omega
      obtain ⟨r1, hr1C, hr1rank⟩ :=
        Drift.stableRank_surjective_on_class (v := wordDrift P w) (c := wordPos w i) rfl h.2.1 h1lt
      obtain ⟨hr1P, hr1sc⟩ := Drift.mem_classPhases.mp hr1C
      have hr1top : layer (wordPos w r1) = topLayer P w :=
        (layer_eq_of_sameClass hlv hr1sc).trans htop
      have hwr1 : w r1 = true := by
        rw [Drift.consistentWord_stableRank_color h hr1P, hr1rank]
        rfl
      have hcol1 := (topLayer_forced_turn_of_layer_zero h hlv hr1P hr1top).1
      have hax : (inDir w r1).horizontal = (inDir w r0).horizontal :=
        same_layer_same_axis w (hr1top.trans hr0top.symm)
      rw [hax, hdir_in0] at hcol1
      simp [Direction.horizontal, hwr1] at hcol1
  have hClen : C.length = 1 := by omega
  have hirank_lt : Drift.stableRank P w i < C.length :=
    Drift.stableRank_lt_class_length rfl h.2.1 hiC
  have hirank : Drift.stableRank P w i = 0 := by omega
  have hir0 : i = r0 :=
    Drift.stableRank_injective_on_class rfl h.2.1 hiC hr0C (hirank.trans hr0rank.symm)
  subst hir0
  have hdir_out : outDir w i = .south := by
    simp [outDir, hwr0, hdir_in0, turn, Direction.right]
  have huniq : ∀ j, j < P → Drift.SameClass (wordDrift P w) (wordPos w j) (wordPos w i) → j = i := by
    intro j hj hsc
    have hjC : j ∈ C := Drift.mem_classPhases.mpr ⟨hj, hsc⟩
    have hjrank_lt : Drift.stableRank P w j < C.length :=
      Drift.stableRank_lt_class_length rfl h.2.1 hjC
    have hjrank : Drift.stableRank P w j = 0 := by omega
    exact Drift.stableRank_injective_on_class rfl h.2.1 hjC hiC (hjrank.trans hirank.symm)
  have hCeq : C = [i] :=
    list_eq_singleton_of_nodup' (Drift.classPhases_nodup _ _ _ _) hiC
      (fun j hj => let ⟨hjP, hsc⟩ := Drift.mem_classPhases.mp hj; huniq j hjP hsc)
  have hodd : i ∈ oddClassReps P w :=
    mem_oddClassReps.mpr ⟨hi, hirank, by change C.length % 2 = 1; omega⟩
  have hchi : checkerSign (wordPos w i) = -1 := by
    rw [checkerSign_eq_neg_one_iff_layer_odd]
    exact (inDir_horizontal_iff w i).mp (by simp [hdir_in0, Direction.horizontal])
  exact ⟨hirank, hwr0, hdir_in0, hdir_out, hCeq, hClen, huniq, hodd, hchi⟩

/-- **Jillhewar Theorem 9.1 (bottom extremal line, arbitrary anti-diagonal drift `layer v = 0`):**
Every phase `i < P` attaining `botLayer P w` is the unique visit in its full translation class,
has `stableRank = 0`, reads white (`false`), arrives `.west`, leaves `.north`, belongs to
`oddClassReps P w`, and carries checkerboard sign `χ = -1` (horizontal / odd layer). -/
theorem botLayer_phase_rigid_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0)
    (hi : i < P) (hbot : layer (wordPos w i) = botLayer P w) :
    Drift.stableRank P w i = 0 ∧
    w i = false ∧
    inDir w i = .west ∧
    outDir w i = .north ∧
    sameClassPhases P w i = [i] ∧
    (sameClassPhases P w i).length = 1 ∧
    (∀ j, j < P → Drift.SameClass (wordDrift P w) (wordPos w j) (wordPos w i) → j = i) ∧
    i ∈ oddClassReps P w ∧
    checkerSign (wordPos w i) = -1 := by
  let C := sameClassPhases P w i
  have hiC : i ∈ C := Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩
  have hCpos : 0 < C.length := List.length_pos_of_mem hiC
  obtain ⟨r0, hr0C, hr0rank⟩ :=
    Drift.stableRank_surjective_on_class (v := wordDrift P w) (c := wordPos w i) rfl h.2.1 hCpos
  obtain ⟨hr0P, hr0sc⟩ := Drift.mem_classPhases.mp hr0C
  have hr0bot : layer (wordPos w r0) = botLayer P w :=
    (layer_eq_of_sameClass hlv hr0sc).trans hbot
  have hwr0 : w r0 = false := by
    rw [Drift.consistentWord_stableRank_color h hr0P, hr0rank]
    rfl
  obtain ⟨hcol0, hin0, _⟩ := botLayer_forced_turn_of_layer_zero h hlv hr0P hr0bot
  have hdir_in0 : inDir w r0 = .west := by
    cases hd' : inDir w r0 <;>
      simp [hd', hwr0, Direction.horizontal, layerDelta] at hcol0 hin0 ⊢
  have hClen_le : C.length ≤ 1 := by
    by_cases hle : C.length ≤ 1
    · exact hle
    · exfalso
      have h1lt : 1 < C.length := by omega
      obtain ⟨r1, hr1C, hr1rank⟩ :=
        Drift.stableRank_surjective_on_class (v := wordDrift P w) (c := wordPos w i) rfl h.2.1 h1lt
      obtain ⟨hr1P, hr1sc⟩ := Drift.mem_classPhases.mp hr1C
      have hr1bot : layer (wordPos w r1) = botLayer P w :=
        (layer_eq_of_sameClass hlv hr1sc).trans hbot
      have hwr1 : w r1 = true := by
        rw [Drift.consistentWord_stableRank_color h hr1P, hr1rank]
        rfl
      have hcol1 := (botLayer_forced_turn_of_layer_zero h hlv hr1P hr1bot).1
      have hax : (inDir w r1).horizontal = (inDir w r0).horizontal :=
        same_layer_same_axis w (hr1bot.trans hr0bot.symm)
      rw [hax, hdir_in0] at hcol1
      simp [Direction.horizontal, hwr1] at hcol1
  have hClen : C.length = 1 := by omega
  have hirank_lt : Drift.stableRank P w i < C.length :=
    Drift.stableRank_lt_class_length rfl h.2.1 hiC
  have hirank : Drift.stableRank P w i = 0 := by omega
  have hir0 : i = r0 :=
    Drift.stableRank_injective_on_class rfl h.2.1 hiC hr0C (hirank.trans hr0rank.symm)
  subst hir0
  have hdir_out : outDir w i = .north := by
    simp [outDir, hwr0, hdir_in0, turn, Direction.right]
  have huniq : ∀ j, j < P → Drift.SameClass (wordDrift P w) (wordPos w j) (wordPos w i) → j = i := by
    intro j hj hsc
    have hjC : j ∈ C := Drift.mem_classPhases.mpr ⟨hj, hsc⟩
    have hjrank_lt : Drift.stableRank P w j < C.length :=
      Drift.stableRank_lt_class_length rfl h.2.1 hjC
    have hjrank : Drift.stableRank P w j = 0 := by omega
    exact Drift.stableRank_injective_on_class rfl h.2.1 hjC hiC (hjrank.trans hirank.symm)
  have hCeq : C = [i] :=
    list_eq_singleton_of_nodup' (Drift.classPhases_nodup _ _ _ _) hiC
      (fun j hj => let ⟨hjP, hsc⟩ := Drift.mem_classPhases.mp hj; huniq j hjP hsc)
  have hodd : i ∈ oddClassReps P w :=
    mem_oddClassReps.mpr ⟨hi, hirank, by change C.length % 2 = 1; omega⟩
  have hchi : checkerSign (wordPos w i) = -1 := by
    rw [checkerSign_eq_neg_one_iff_layer_odd]
    exact (inDir_horizontal_iff w i).mp (by simp [hdir_in0, Direction.horizontal])
  exact ⟨hirank, hwr0, hdir_in0, hdir_out, hCeq, hClen, huniq, hodd, hchi⟩

/-- Every translation class meeting `topLayer P w` is visited at most once. -/
theorem topLayer_class_length_le_one_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0)
    {c : Point} (hc : layer c = topLayer P w) :
    (Drift.classPhases (wordDrift P w) P w c).length ≤ 1 := by
  cases hlist : Drift.classPhases (wordDrift P w) P w c with
  | nil => simp
  | cons i xs =>
    have hi : i ∈ Drift.classPhases (wordDrift P w) P w c := by rw [hlist]; simp
    obtain ⟨hiP, hisc⟩ := Drift.mem_classPhases.mp hi
    have hitop : layer (wordPos w i) = topLayer P w :=
      (layer_eq_of_sameClass hlv hisc).trans hc
    have hlen1 := (topLayer_phase_rigid_of_layer_zero h hlv hiP hitop).2.2.2.2.2.1
    rw [← hlist, Drift.classPhases_congr P w hisc.symm]
    change (sameClassPhases P w i).length ≤ 1
    omega

/-- Every translation class meeting `botLayer P w` is visited at most once. -/
theorem botLayer_class_length_le_one_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0)
    {c : Point} (hc : layer c = botLayer P w) :
    (Drift.classPhases (wordDrift P w) P w c).length ≤ 1 := by
  cases hlist : Drift.classPhases (wordDrift P w) P w c with
  | nil => simp
  | cons i xs =>
    have hi : i ∈ Drift.classPhases (wordDrift P w) P w c := by rw [hlist]; simp
    obtain ⟨hiP, hisc⟩ := Drift.mem_classPhases.mp hi
    have hibot : layer (wordPos w i) = botLayer P w :=
      (layer_eq_of_sameClass hlv hisc).trans hc
    have hlen1 := (botLayer_phase_rigid_of_layer_zero h hlv hiP hibot).2.2.2.2.2.1
    rw [← hlist, Drift.classPhases_congr P w hisc.symm]
    change (sameClassPhases P w i).length ≤ 1
    omega

theorem topLayer_odd_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    topLayer P w % 2 = 1 := by
  obtain ⟨i, hi, htop⟩ := exists_topLayer_phase (w := w) h.pos_period
  have hchi := (topLayer_phase_rigid_of_layer_zero h hlv hi htop).2.2.2.2.2.2.2.2
  rw [checkerSign_eq_neg_one_iff_layer_odd, htop] at hchi
  exact hchi

theorem botLayer_odd_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    botLayer P w % 2 = 1 := by
  obtain ⟨i, hi, hbot⟩ := exists_botLayer_phase (w := w) h.pos_period
  have hchi := (botLayer_phase_rigid_of_layer_zero h hlv hi hbot).2.2.2.2.2.2.2.2
  rw [checkerSign_eq_neg_one_iff_layer_odd, hbot] at hchi
  exact hchi

theorem layerWidth_even_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    layerWidth P w % 2 = 0 := by
  have ht := topLayer_odd_of_layer_zero h hlv
  have hb := botLayer_odd_of_layer_zero h hlv
  unfold layerWidth
  omega

theorem layerWidth_ge_two_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    2 ≤ layerWidth P w := by
  obtain ⟨i, hi, htop⟩ := exists_topLayer_phase (w := w) h.pos_period
  have hout := (topLayer_phase_rigid_of_layer_zero h hlv hi htop).2.2.2.1
  have hnext := layer_wordPos_nextPhase_of_layer_zero hlv hi
  rw [htop, hout] at hnext
  have hbot_le : botLayer P w ≤ layer (wordPos w (nextPhase P i)) :=
    botLayer_le_layer (nextPhase_lt h.pos_period)
  have ht := topLayer_odd_of_layer_zero h hlv
  have hb := botLayer_odd_of_layer_zero h hlv
  simp only [layerDelta] at hnext
  unfold layerWidth
  omega

/-- The top and bottom extremal lines supply at least two distinct odd translation classes,
both carrying checkerboard sign `χ = -1` (odd/horizontal layers). -/
theorem exists_two_neg_oddClassReps_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    ∃ iTop iBot,
      iTop ∈ oddClassReps P w ∧
      iBot ∈ oddClassReps P w ∧
      iTop ≠ iBot ∧
      layer (wordPos w iTop) = topLayer P w ∧
      layer (wordPos w iBot) = botLayer P w ∧
      checkerSign (wordPos w iTop) = -1 ∧
      checkerSign (wordPos w iBot) = -1 := by
  obtain ⟨iTop, hiTop, htop⟩ := exists_topLayer_phase (w := w) h.pos_period
  obtain ⟨iBot, hiBot, hbot⟩ := exists_botLayer_phase (w := w) h.pos_period
  have hrTop := topLayer_phase_rigid_of_layer_zero h hlv hiTop htop
  have hrBot := botLayer_phase_rigid_of_layer_zero h hlv hiBot hbot
  have hw := layerWidth_ge_two_of_layer_zero h hlv
  have hne : iTop ≠ iBot := by
    intro heq
    subst heq
    unfold layerWidth at hw
    omega
  exact ⟨iTop, iBot, hrTop.2.2.2.2.2.2.2.1, hrBot.2.2.2.2.2.2.2.1,
    hne, htop, hbot, hrTop.2.2.2.2.2.2.2.2, hrBot.2.2.2.2.2.2.2.2⟩

theorem two_le_neg_oddClassReps_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    2 ≤ ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length := by
  obtain ⟨iTop, iBot, hTopO, hBotO, hne, _, _, hTopChi, hBotChi⟩ :=
    exists_two_neg_oddClassReps_of_layer_zero h hlv
  have hnd : ([iTop, iBot] : List Nat).Nodup := by simp [hne]
  have hsub : [iTop, iBot] ⊆
      (oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1)) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact List.mem_filter.mpr ⟨hTopO, decide_eq_true hTopChi⟩
    · exact List.mem_filter.mpr ⟨hBotO, decide_eq_true hBotChi⟩
  have hle := hnd.length_le_of_subset hsub
  simpa using hle

/-- **Exclusion of `𝒪 ⊆ Q` (all odd classes `χ = +1`), arbitrary anti-diagonal drift `layer v = 0`.** -/
theorem not_all_oddClassReps_pos_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) :
    ¬ (∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = 1) := by
  intro hall
  obtain ⟨iTop, _, hTopO, _, _, _, _, hTopChi, _⟩ :=
    exists_two_neg_oddClassReps_of_layer_zero h hlv
  have hpos := hall iTop hTopO
  omega

/-! ### Specialization to full drift `(2, -2)` (Blueprint L21 and L24(1)) -/

theorem topLayer_odd {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    topLayer P w % 2 = 1 :=
  topLayer_odd_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)

theorem botLayer_odd {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    botLayer P w % 2 = 1 :=
  botLayer_odd_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)

theorem layerWidth_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    layerWidth P w % 2 = 0 :=
  layerWidth_even_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)

theorem layerWidth_ge_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    2 ≤ layerWidth P w :=
  layerWidth_ge_two_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)

/-- **L21 (top extremal line for drift `(2, -2)`):** Every phase on `topLayer P w` is the unique
visit in its `(layer, lane)` translation class, has `stableRank = 0`, reads white, enters `.east`,
leaves `.south`, belongs to `oddClassReps P w`, and has `checkerSign = -1`. -/
theorem topLayer_phase_rigid {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i < P) (htop : layer (wordPos w i) = topLayer P w) :
    Drift.stableRank P w i = 0 ∧
    w i = false ∧
    inDir w i = .east ∧
    outDir w i = .south ∧
    classPhases2 P w (topLayer P w) (lane (wordPos w i)) = [i] ∧
    classMult P w (topLayer P w) (lane (wordPos w i)) = 1 ∧
    (∀ j, j < P → layer (wordPos w j) = topLayer P w →
      lane (wordPos w j) = lane (wordPos w i) → j = i) ∧
    i ∈ oddClassReps P w ∧
    checkerSign (wordPos w i) = -1 := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_two_negTwo
  obtain ⟨hr0, hwi, hin, hout, hCeq, hClen, huniq, hodd, hchi⟩ :=
    topLayer_phase_rigid_of_layer_zero h hlv hi htop
  have hsc : Drift.SameClass (2, -2) (wordPos w i) (classRep (topLayer P w) (lane (wordPos w i))) :=
    (sameClass_two_negTwo_classRep _ _ _).mpr ⟨htop, rfl⟩
  have hcp : classPhases2 P w (topLayer P w) (lane (wordPos w i)) = sameClassPhases P w i := by
    unfold classPhases2 sameClassPhases
    rw [hd]
    exact Drift.classPhases_congr P w hsc.symm
  refine ⟨hr0, hwi, hin, hout, hcp.trans hCeq, by unfold classMult; rw [hcp]; exact hClen, ?_, hodd, hchi⟩
  intro j hj hjl hjr
  apply huniq j hj
  rw [hd, sameClass_two_negTwo_iff]
  exact ⟨hjl.trans htop.symm, hjr⟩

/-- **L21 (bottom extremal line for drift `(2, -2)`):** Every phase on `botLayer P w` is the unique
visit in its `(layer, lane)` translation class, has `stableRank = 0`, reads white, enters `.west`,
leaves `.north`, belongs to `oddClassReps P w`, and has `checkerSign = -1`. -/
theorem botLayer_phase_rigid {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i < P) (hbot : layer (wordPos w i) = botLayer P w) :
    Drift.stableRank P w i = 0 ∧
    w i = false ∧
    inDir w i = .west ∧
    outDir w i = .north ∧
    classPhases2 P w (botLayer P w) (lane (wordPos w i)) = [i] ∧
    classMult P w (botLayer P w) (lane (wordPos w i)) = 1 ∧
    (∀ j, j < P → layer (wordPos w j) = botLayer P w →
      lane (wordPos w j) = lane (wordPos w i) → j = i) ∧
    i ∈ oddClassReps P w ∧
    checkerSign (wordPos w i) = -1 := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_two_negTwo
  obtain ⟨hr0, hwi, hin, hout, hCeq, hClen, huniq, hodd, hchi⟩ :=
    botLayer_phase_rigid_of_layer_zero h hlv hi hbot
  have hsc : Drift.SameClass (2, -2) (wordPos w i) (classRep (botLayer P w) (lane (wordPos w i))) :=
    (sameClass_two_negTwo_classRep _ _ _).mpr ⟨hbot, rfl⟩
  have hcp : classPhases2 P w (botLayer P w) (lane (wordPos w i)) = sameClassPhases P w i := by
    unfold classPhases2 sameClassPhases
    rw [hd]
    exact Drift.classPhases_congr P w hsc.symm
  refine ⟨hr0, hwi, hin, hout, hcp.trans hCeq, by unfold classMult; rw [hcp]; exact hClen, ?_, hodd, hchi⟩
  intro j hj hjl hjr
  apply huniq j hj
  rw [hd, sameClass_two_negTwo_iff]
  exact ⟨hjl.trans hbot.symm, hjr⟩

theorem topLayer_classMult_le_one {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (r : Bool) :
    classMult P w (topLayer P w) r ≤ 1 := by
  have h1 := topLayer_class_length_le_one_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)
    (c := classRep (topLayer P w) r) (layer_classRep _ _)
  unfold classMult classPhases2
  rwa [hd] at h1

theorem botLayer_classMult_le_one {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (r : Bool) :
    classMult P w (botLayer P w) r ≤ 1 := by
  have h1 := botLayer_class_length_le_one_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)
    (c := classRep (botLayer P w) r) (layer_classRep _ _)
  unfold classMult classPhases2
  rwa [hd] at h1

theorem topLayer_layerPhases_bounds {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    1 ≤ (layerPhases P w (topLayer P w)).length ∧
    (layerPhases P w (topLayer P w)).length ≤ 2 := by
  obtain ⟨i, hi, htop⟩ := exists_topLayer_phase (w := w) h.pos_period
  have hpos : 0 < (layerPhases P w (topLayer P w)).length :=
    List.length_pos_of_mem (mem_layerPhases.mpr ⟨hi, htop⟩)
  have hsplit := layerPhases_length_eq_add_classMult P w (topLayer P w)
  have hF := topLayer_classMult_le_one h hd false
  have hT := topLayer_classMult_le_one h hd true
  omega

theorem botLayer_layerPhases_bounds {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    1 ≤ (layerPhases P w (botLayer P w)).length ∧
    (layerPhases P w (botLayer P w)).length ≤ 2 := by
  obtain ⟨i, hi, hbot⟩ := exists_botLayer_phase (w := w) h.pos_period
  have hpos : 0 < (layerPhases P w (botLayer P w)).length :=
    List.length_pos_of_mem (mem_layerPhases.mpr ⟨hi, hbot⟩)
  have hsplit := layerPhases_length_eq_add_classMult P w (botLayer P w)
  have hF := botLayer_classMult_le_one h hd false
  have hT := botLayer_classMult_le_one h hd true
  omega

/-- **L21(3) / L24(1):** For drift `(2, -2)`, at least two odd classes have `χ = -1`, so the
`𝒪 ⊆ Q` (all `χ = +1`) branch is impossible for every growth `g`. -/
theorem two_le_neg_oddClassReps {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    2 ≤ ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length :=
  two_le_neg_oddClassReps_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)

theorem not_all_oddClassReps_pos {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    ¬ (∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = 1) :=
  not_all_oddClassReps_pos_of_layer_zero h (by rw [hd]; exact layer_two_negTwo)

/-- Direct combination with `PeriodicGrowthResidue.ConsistentWord.drift_two_negTwo_growth_four_structure`:
a hypothetical `(2, -2)` consistent word of growth `4` must have all four odd classes on odd layers
(`χ = -1`), with two in each `x mod 2` lane. -/
theorem drift_two_negTwo_growth_four_all_neg {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hg : wordGrowth P w = 4) :
    (∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = -1) ∧
    ((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 0))).length = 2 ∧
    ((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 1))).length = 2 := by
  obtain ⟨hpure, hl0, hl1⟩ := h.drift_two_negTwo_growth_four_structure hd hg
  rcases hpure with hpos | hneg
  · exact False.elim (not_all_oddClassReps_pos h hd hpos)
  · exact ⟨hneg, hl0, hl1⟩

/-! ## 3. Blueprint L22: Two-lane exact flow conservation and pure-odd-layer flux cancellation -/

/-- Number of departures from `(2, -2)` class `(t, r)` in direction `d`. -/
def depCount (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) (d : Direction) : Nat :=
  (Drift.departures (2, -2) P w (classRep t r) d).length

/-- Number of arrivals at `(2, -2)` class `(t, r)` in direction `d`. -/
def arrCount (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) (d : Direction) : Nat :=
  (Drift.arrivals (2, -2) P w (classRep t r) d).length

abbrev wCnt (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat := depCount P w t r .west
abbrev eCnt (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat := depCount P w t r .east
abbrev sCnt (P : Nat) (w : Nat → Bool) (j : Int) (r : Bool) : Nat := depCount P w j r .south
abbrev nCnt (P : Nat) (w : Nat → Bool) (j : Int) (r : Bool) : Nat := depCount P w j r .north

private theorem filter_two_values_length {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → β) {b1 b2 : β} (hne : b1 ≠ b2)
    (hcov : ∀ x ∈ xs, f x = b1 ∨ f x = b2) :
    (xs.filter (fun x => decide (f x = b1))).length +
      (xs.filter (fun x => decide (f x = b2))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hcov x (by simp)
    have hxs := ih (fun y hy => hcov y (by simp [hy]))
    rcases hx with hx1 | hx2
    · simp only [List.filter_cons, hx1, decide_true, ite_true, decide_eq_false hne,
        Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · simp only [List.filter_cons, hx2, decide_true, ite_true, decide_eq_false hne.symm,
        Bool.false_eq_true, ite_false, List.length_cons]
      omega

private theorem filter_empty_of_forall_ne {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → β) (b : β) (h : ∀ x ∈ xs, f x ≠ b) :
    (xs.filter (fun x => decide (f x = b))).length = 0 := by
  have heq : xs.filter (fun x => decide (f x = b)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨hxm, hfb⟩ := List.mem_filter.mp hx
    exact h x hxm (of_decide_eq_true hfb)
  rw [heq]
  rfl

private theorem outDir_horizontal_eq (w : Nat → Bool) (i : Nat) :
    (outDir w i).horizontal = !(inDir w i).horizontal := by
  unfold outDir
  cases w i <;> cases inDir w i <;> rfl

theorem even_layer_dirs {P i : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (ht : t % 2 = 0) (hi : i ∈ classPhases2 P w t r) :
    (inDir w i = .north ∨ inDir w i = .south) ∧
    (outDir w i = .east ∨ outDir w i = .west) := by
  obtain ⟨_, hli, _⟩ := mem_classPhases2.mp hi
  have hinH : (inDir w i).horizontal = false := by
    rw [inDir_horizontal_eq, hli]
    have hne : t % 2 ≠ 1 := by omega
    simp [hne]
  have houtH : (outDir w i).horizontal = true := by
    rw [outDir_horizontal_eq, hinH]; rfl
  constructor
  · cases hd' : inDir w i <;> simp [hd', Direction.horizontal] at hinH ⊢
  · cases hd' : outDir w i <;> simp [hd', Direction.horizontal] at houtH ⊢

theorem odd_layer_dirs {P i : Nat} {w : Nat → Bool} {j : Int} {r : Bool}
    (hj : j % 2 = 1) (hi : i ∈ classPhases2 P w j r) :
    (inDir w i = .east ∨ inDir w i = .west) ∧
    (outDir w i = .north ∨ outDir w i = .south) := by
  obtain ⟨_, hli, _⟩ := mem_classPhases2.mp hi
  have hinH : (inDir w i).horizontal = true := by
    rw [inDir_horizontal_eq, hli]
    simp [hj]
  have houtH : (outDir w i).horizontal = false := by
    rw [outDir_horizontal_eq, hinH]; rfl
  constructor
  · cases hd' : inDir w i <;> simp [hd', Direction.horizontal] at hinH ⊢
  · cases hd' : outDir w i <;> simp [hd', Direction.horizontal] at houtH ⊢

theorem depCount_eq_arrCount_north {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool) :
    nCnt P w t r = arrCount P w (t + 1) r .north := by
  unfold nCnt depCount arrCount
  rw [Drift.departures_length_eq_arrivals_length hh hd]
  rw [Drift.arrivals_congr P w .north (sameClass_move_classRep_north t r)]

theorem depCount_eq_arrCount_south {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool) :
    sCnt P w t r = arrCount P w (t - 1) r .south := by
  unfold sCnt depCount arrCount
  rw [Drift.departures_length_eq_arrivals_length hh hd]
  rw [Drift.arrivals_congr P w .south (sameClass_move_classRep_south t r)]

theorem depCount_eq_arrCount_east {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool) :
    eCnt P w t r = arrCount P w (t + 1) (!r) .east := by
  unfold eCnt depCount arrCount
  rw [Drift.departures_length_eq_arrivals_length hh hd]
  rw [Drift.arrivals_congr P w .east (sameClass_move_classRep_east t r)]

theorem depCount_eq_arrCount_west {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool) :
    wCnt P w t r = arrCount P w (t - 1) (!r) .west := by
  unfold wCnt depCount arrCount
  rw [Drift.departures_length_eq_arrivals_length hh hd]
  rw [Drift.arrivals_congr P w .west (sameClass_move_classRep_west t r)]

theorem even_layer_dep_sum {P : Nat} {w : Nat → Bool} {t : Int} (ht : t % 2 = 0) (r : Bool) :
    wCnt P w t r + eCnt P w t r = classMult P w t r := by
  unfold wCnt eCnt depCount Drift.departures classMult classPhases2
  have h := filter_two_values_length (classPhases2 P w t r) (outDir w)
    (b1 := .west) (b2 := .east) (by decide)
    (fun i hi => (even_layer_dirs ht hi).2.symm)
  exact h

theorem even_layer_dep_vert_zero {P : Nat} {w : Nat → Bool} {t : Int} (ht : t % 2 = 0) (r : Bool) :
    nCnt P w t r = 0 ∧ sCnt P w t r = 0 := by
  constructor
  · exact filter_empty_of_forall_ne (classPhases2 P w t r) (outDir w) .north (fun i hi => by
      rcases (even_layer_dirs ht hi).2 with h | h <;> simp [h])
  · exact filter_empty_of_forall_ne (classPhases2 P w t r) (outDir w) .south (fun i hi => by
      rcases (even_layer_dirs ht hi).2 with h | h <;> simp [h])

theorem even_layer_arr_sum {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    sCnt P w (t + 1) r + nCnt P w (t - 1) r = classMult P w t r := by
  have hs := depCount_eq_arrCount_south hh hd (t + 1) r
  have hn := depCount_eq_arrCount_north hh hd (t - 1) r
  rw [show t + 1 - 1 = t by omega] at hs
  rw [show t - 1 + 1 = t by omega] at hn
  rw [hs, hn]
  unfold arrCount Drift.arrivals classMult classPhases2
  exact filter_two_values_length (classPhases2 P w t r) (inDir w)
    (b1 := .south) (b2 := .north) (by decide)
    (fun i hi => (even_layer_dirs ht hi).1.symm)

theorem odd_layer_dep_sum {P : Nat} {w : Nat → Bool} {j : Int} (hj : j % 2 = 1) (r : Bool) :
    sCnt P w j r + nCnt P w j r = classMult P w j r := by
  unfold sCnt nCnt depCount Drift.departures classMult classPhases2
  exact filter_two_values_length (classPhases2 P w j r) (outDir w)
    (b1 := .south) (b2 := .north) (by decide)
    (fun i hi => (odd_layer_dirs hj hi).2.symm)

theorem odd_layer_dep_horiz_zero {P : Nat} {w : Nat → Bool} {j : Int} (hj : j % 2 = 1) (r : Bool) :
    wCnt P w j r = 0 ∧ eCnt P w j r = 0 := by
  constructor
  · exact filter_empty_of_forall_ne (classPhases2 P w j r) (outDir w) .west (fun i hi => by
      rcases (odd_layer_dirs hj hi).2 with h | h <;> simp [h])
  · exact filter_empty_of_forall_ne (classPhases2 P w j r) (outDir w) .east (fun i hi => by
      rcases (odd_layer_dirs hj hi).2 with h | h <;> simp [h])

theorem odd_layer_arr_sum {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    wCnt P w (j + 1) (!r) + eCnt P w (j - 1) (!r) = classMult P w j r := by
  have hw := depCount_eq_arrCount_west hh hd (j + 1) (!r)
  have he := depCount_eq_arrCount_east hh hd (j - 1) (!r)
  rw [show j + 1 - 1 = j by omega, Bool.not_not] at hw
  rw [show j - 1 + 1 = j by omega, Bool.not_not] at he
  rw [hw, he]
  unfold arrCount Drift.arrivals classMult classPhases2
  exact filter_two_values_length (classPhases2 P w j r) (inDir w)
    (b1 := .west) (b2 := .east) (by decide)
    (fun i hi => (odd_layer_dirs hj hi).1.symm)

/-- **Exact two-lane flow conservation** at even (`Q`) and odd (`C`) layers (Ke §4 Eq. (12) /
Jillhewar Eq. (diagflowQ)–(diagflowC), exact in `Nat`). -/
theorem even_layer_flow_eq {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    wCnt P w t r + eCnt P w t r = sCnt P w (t + 1) r + nCnt P w (t - 1) r := by
  rw [even_layer_dep_sum ht r, even_layer_arr_sum hh hd ht r]

theorem odd_layer_flow_eq {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    sCnt P w j r + nCnt P w j r = wCnt P w (j + 1) (!r) + eCnt P w (j - 1) (!r) := by
  rw [odd_layer_dep_sum hj r, odd_layer_arr_sum hh hd hj r]

/-! ### Support bounds outside `[botLayer, topLayer]` -/

theorem classPhases2_eq_nil_of_gt_top {P : Nat} {w : Nat → Bool} {t : Int} (r : Bool)
    (ht : topLayer P w < t) :
    classPhases2 P w t r = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hiP, hli, _⟩ := mem_classPhases2.mp hi
  have hle := layer_le_topLayer (w := w) hiP
  omega

theorem classPhases2_eq_nil_of_lt_bot {P : Nat} {w : Nat → Bool} {t : Int} (r : Bool)
    (ht : t < botLayer P w) :
    classPhases2 P w t r = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hiP, hli, _⟩ := mem_classPhases2.mp hi
  have hge := botLayer_le_layer (w := w) hiP
  omega

theorem classMult_eq_zero_of_gt_top {P : Nat} {w : Nat → Bool} {t : Int} (r : Bool)
    (ht : topLayer P w < t) : classMult P w t r = 0 := by
  unfold classMult
  rw [classPhases2_eq_nil_of_gt_top r ht]
  rfl

theorem classMult_eq_zero_of_lt_bot {P : Nat} {w : Nat → Bool} {t : Int} (r : Bool)
    (ht : t < botLayer P w) : classMult P w t r = 0 := by
  unfold classMult
  rw [classPhases2_eq_nil_of_lt_bot r ht]
  rfl

theorem depCount_eq_zero_of_gt_top {P : Nat} {w : Nat → Bool} {t : Int} (r : Bool) (d : Direction)
    (ht : topLayer P w < t) : depCount P w t r d = 0 := by
  unfold depCount Drift.departures
  change ((classPhases2 P w t r).filter _).length = 0
  rw [classPhases2_eq_nil_of_gt_top r ht]
  rfl

theorem depCount_eq_zero_of_lt_bot {P : Nat} {w : Nat → Bool} {t : Int} (r : Bool) (d : Direction)
    (ht : t < botLayer P w) : depCount P w t r d = 0 := by
  unfold depCount Drift.departures
  change ((classPhases2 P w t r).filter _).length = 0
  rw [classPhases2_eq_nil_of_lt_bot r ht]
  rfl

theorem nCnt_topLayer_eq_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (r : Bool) :
    nCnt P w (topLayer P w) r = 0 := by
  exact filter_empty_of_forall_ne (classPhases2 P w (topLayer P w) r) (outDir w) .north (fun i hi => by
    obtain ⟨hiP, hli, _⟩ := mem_classPhases2.mp hi
    have hout := (topLayer_phase_rigid h hd hiP hli).2.2.2.1
    simp [hout])

theorem sCnt_botLayer_eq_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (r : Bool) :
    sCnt P w (botLayer P w) r = 0 := by
  exact filter_empty_of_forall_ne (classPhases2 P w (botLayer P w) r) (outDir w) .south (fun i hi => by
    obtain ⟨hiP, hli, _⟩ := mem_classPhases2.mp hi
    have hout := (botLayer_phase_rigid h hd hiP hli).2.2.2.1
    simp [hout])

/-! ### Pure-odd-layer (`𝒪 ⊆ C`) equivalence and flux cancellation (L22(1)–(2)) -/

/-- The wake `𝒪` is pure odd-layer (`𝒪 ⊆ C`): every odd translation class has `χ = -1`. -/
def PureOddWake (P : Nat) (w : Nat → Bool) : Prop :=
  ∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = -1

/-- Equivalence between `PureOddWake` (`𝒪 ⊆ C`) and even visit multiplicity on every even layer `Q`. -/
theorem pureOddWake_iff_even_classMult_even {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) :
    PureOddWake P w ↔ ∀ t : Int, ∀ r : Bool, t % 2 = 0 → classMult P w t r % 2 = 0 := by
  constructor
  · intro hpure t r ht
    by_cases hpar : classMult P w t r % 2 = 0
    · exact hpar
    · exfalso
      have hodd : classMult P w t r % 2 = 1 := by omega
      have hpos : 0 < (Drift.classPhases (2, -2) P w (classRep t r)).length := by
        unfold classMult classPhases2 at hodd; omega
      obtain ⟨i, hiC, hirank⟩ :=
        Drift.stableRank_surjective_on_class (v := (2, -2)) (c := classRep t r) hd
          drift_two_negTwo_ne_zero hpos
      obtain ⟨hiP, hisc⟩ := Drift.mem_classPhases.mp hiC
      have hli : layer (wordPos w i) = t := ((sameClass_two_negTwo_classRep _ _ _).mp hisc).1
      have hsame : sameClassPhases P w i = classPhases2 P w t r := by
        unfold sameClassPhases classPhases2
        rw [hd]
        exact Drift.classPhases_congr P w hisc
      have hiO : i ∈ oddClassReps P w :=
        mem_oddClassReps.mpr ⟨hiP, hirank, by rw [hsame]; exact hodd⟩
      have hchi := hpure i hiO
      rw [checkerSign_eq_neg_one_iff_layer_odd, hli] at hchi
      omega
  · intro heven i hiO
    obtain ⟨hiP, _, hmod⟩ := mem_oddClassReps.mp hiO
    have hsame : sameClassPhases P w i = classPhases2 P w (layer (wordPos w i)) (lane (wordPos w i)) := by
      unfold sameClassPhases classPhases2
      rw [hd]
      exact Drift.classPhases_congr P w ((sameClass_two_negTwo_classRep _ _ _).mpr ⟨rfl, rfl⟩)
    rw [hsame] at hmod
    rw [checkerSign_eq_neg_one_iff_layer_odd]
    by_cases hpar : layer (wordPos w i) % 2 = 1
    · exact hpar
    · exfalso
      have hev := heven (layer (wordPos w i)) (lane (wordPos w i)) (by omega)
      unfold classMult at hev
      omega

/-- **L22(1):** Under `PureOddWake`, west and east departure counts from every even class `Q_{t,r}`
have the same parity (`w_{t,r} ≡ e_{t,r} (mod 2)`). -/
theorem pureOdd_wCnt_mod_two_eq_eCnt {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    wCnt P w t r % 2 = eCnt P w t r % 2 := by
  have hev := (pureOddWake_iff_even_classMult_even hd).mp hpure t r ht
  have hsum := even_layer_dep_sum (P := P) (w := w) ht r
  omega

/-- **L22(2a):** Under `PureOddWake`, south and shifted-north departure counts from odd classes
agree mod 2: `s_{j,r} ≡ n_{j-2,r} (mod 2)` for every odd `j`. -/
theorem pureOdd_sCnt_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    sCnt P w j r % 2 = nCnt P w (j - 2) r % 2 := by
  have ht : (j - 1) % 2 = 0 := by omega
  have hev := (pureOddWake_iff_even_classMult_even hd).mp hpure (j - 1) r ht
  have harr := even_layer_arr_sum h.1 hd ht r
  rw [show j - 1 + 1 = j by omega, show j - 1 - 1 = j - 2 by omega] at harr
  omega

/-- Step-2 recurrence along each even-layer ladder: `(e_{t,r} + n_{t-1,!r}) mod 2` is constant in `t`. -/
theorem pureOdd_step_invariant {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    (eCnt P w t r + nCnt P w (t - 1) (!r)) % 2 =
      (eCnt P w (t + 2) r + nCnt P w (t + 1) (!r)) % 2 := by
  have hj : (t + 1) % 2 = 1 := by omega
  have hflow := odd_layer_flow_eq h.1 hd hj (!r)
  rw [show t + 1 + 1 = t + 2 by omega, show t + 1 - 1 = t by omega, Bool.not_not] at hflow
  have hs := pureOdd_sCnt_mod_two h hd hpure hj (!r)
  rw [show t + 1 - 2 = t - 1 by omega] at hs
  have hw := pureOdd_wCnt_mod_two_eq_eCnt hd hpure (show (t + 2) % 2 = 0 by omega) r
  omega

/-- **L22(2b):** Finite support drives the step-2 invariant to zero: for every even `t` and lane `r`,
`e_{t,r} ≡ n_{t-1,!r} (mod 2)` and `w_{t,r} ≡ n_{t-1,!r} (mod 2)`. -/
theorem pureOdd_eCnt_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    eCnt P w t r % 2 = nCnt P w (t - 1) (!r) % 2 := by
  let T0 : Int := topLayer P w + 3
  have htop_odd := topLayer_odd h hd
  have hT0_even : T0 % 2 = 0 := by dsimp [T0]; omega
  by_cases hge : T0 ≤ t
  · have h1 := depCount_eq_zero_of_gt_top (P := P) (w := w) r .east (show topLayer P w < t by omega)
    have h2 := depCount_eq_zero_of_gt_top (P := P) (w := w) (!r) .north (show topLayer P w < t - 1 by omega)
    unfold eCnt nCnt
    rw [h1, h2]
  · have hdown : ∀ k : Nat,
        (eCnt P w (T0 - 2 * (k : Int)) r + nCnt P w (T0 - 2 * (k : Int) - 1) (!r)) % 2 = 0 := by
      intro k
      induction k with
      | zero =>
        simp only [Int.natCast_zero, Int.mul_zero, Int.sub_zero]
        have h1 := depCount_eq_zero_of_gt_top (P := P) (w := w) r .east (show topLayer P w < T0 by dsimp [T0]; omega)
        have h2 := depCount_eq_zero_of_gt_top (P := P) (w := w) (!r) .north (show topLayer P w < T0 - 1 by dsimp [T0]; omega)
        unfold eCnt nCnt
        rw [h1, h2]
      | succ k ih =>
        have ht' : (T0 - 2 * ((k + 1 : Nat) : Int)) % 2 = 0 := by omega
        have hstep := pureOdd_step_invariant h hd hpure ht' r
        rw [show T0 - 2 * ((k + 1 : Nat) : Int) + 2 = T0 - 2 * (k : Int) by omega,
          show T0 - 2 * ((k + 1 : Nat) : Int) + 1 = T0 - 2 * (k : Int) - 1 by omega] at hstep
        rw [hstep, ih]
    let k : Nat := ((T0 - t) / 2).toNat
    have hk : T0 - 2 * (k : Int) = t := by dsimp [k]; omega
    have h0 := hdown k
    rw [hk] at h0
    omega

theorem pureOdd_wCnt_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    wCnt P w t r % 2 = nCnt P w (t - 1) (!r) % 2 := by
  rw [pureOdd_wCnt_mod_two_eq_eCnt hd hpure ht r, pureOdd_eCnt_mod_two h hd hpure ht r]

/-- **L22(2c):** Under `PureOddWake`, the odd-class indicator `D_{C_{j,r}} = m(C_{j,r}) mod 2` is
the exact mod-2 boundary of the vertical north-count chain: `D_{C_{j,r}} ≡ n_{j-2,r} + n_{j,r} (mod 2)`. -/
theorem pureOdd_odd_classMult_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    classMult P w j r % 2 = (nCnt P w (j - 2) r + nCnt P w j r) % 2 := by
  rw [← odd_layer_dep_sum hj r]
  have hs := pureOdd_sCnt_mod_two h hd hpure hj r
  omega

/-! ### Local mod-4 turn congruences and vanishing of local corrections `L` (L22(3)) -/

/-- Positive-port sum parity `p_v = (∑ α + ∑ β) mod 2` (N/E at even `Q`, E/N at odd `C`). -/
def posPortPar (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat :=
  if t % 2 = 0 then
    (arrCount P w t r .north + depCount P w t r .east) % 2
  else
    (arrCount P w t r .east + depCount P w t r .north) % 2

/-- Local non-inversion correction from Ke Eq. (10) / Jillhewar Eq. (diaglocal):
`p_v (D_v + 1) mod 2` at even `Q`, and `D_v (p_v + 1) mod 2` at odd `C`. -/
def localCorr (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat :=
  if t % 2 = 0 then
    (posPortPar P w t r * (classMult P w t r % 2 + 1)) % 2
  else
    ((classMult P w t r % 2) * (posPortPar P w t r + 1)) % 2

private theorem filter_xor_length_mod_two {α : Type} (p q : α → Bool) (xs : List α) :
    (xs.filter (fun x => xor (p x) (q x))).length % 2 =
      ((xs.filter p).length + (xs.filter q).length) % 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> cases hqx : q x <;> simp [hpx, hqx] <;> omega

theorem choose2_mod_two (m : Nat) :
    (m * (m - 1) / 2) % 2 = if m % 4 = 2 ∨ m % 4 = 3 then 1 else 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hstep : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
      cases m with
      | zero => decide
      | succ k =>
        have hmul : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by
          rw [Nat.add_mul, Nat.mul_add]
          omega
        simp only [Nat.add_sub_cancel, hmul]
        rw [Nat.add_mul_div_left _ _ (by decide)]
    simp only [Nat.add_sub_cancel, hstep]
    by_cases h23 : m % 4 = 2 ∨ m % 4 = 3
    · simp only [h23, ite_true] at ih
      by_cases h23' : (m + 1) % 4 = 2 ∨ (m + 1) % 4 = 3
      · simp only [h23', ite_true]; omega
      · simp only [h23', ite_false]; omega
    · simp only [h23, ite_false] at ih
      by_cases h23' : (m + 1) % 4 = 2 ∨ (m + 1) % 4 = 3
      · simp only [h23', ite_true]; omega
      · simp only [h23', ite_false]; omega

theorem even_layer_left_iff_xor {P i : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (ht : t % 2 = 0) (hi : i ∈ classPhases2 P w t r) :
    w i = xor (decide (inDir w i = .north)) (decide (outDir w i = .east)) := by
  rcases (even_layer_dirs ht hi).1 with hin | hin <;> cases hw : w i <;>
    simp [outDir, hin, hw, turn, Direction.left, Direction.right]

theorem odd_layer_right_iff_xor {P i : Nat} {w : Nat → Bool} {j : Int} {r : Bool}
    (hj : j % 2 = 1) (hi : i ∈ classPhases2 P w j r) :
    (!w i) = xor (decide (inDir w i = .east)) (decide (outDir w i = .north)) := by
  rcases (odd_layer_dirs hj hi).1 with hin | hin <;> cases hw : w i <;>
    simp [outDir, hin, hw, turn, Direction.left, Direction.right]

theorem even_layer_left_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    (classMult P w t r / 2) % 2 = posPortPar P w t r := by
  have hcnt := (h.class_turn_counts (classRep t r)).1
  rw [hd] at hcnt
  change ((classPhases2 P w t r).filter (fun i => w i)).length = classMult P w t r / 2 at hcnt
  rw [← hcnt]
  have hf :
      (classPhases2 P w t r).filter (fun i => w i) =
        (classPhases2 P w t r).filter
          (fun i => xor (decide (inDir w i = .north)) (decide (outDir w i = .east))) := by
    apply List.filter_congr
    intro i hi
    exact even_layer_left_iff_xor ht hi
  rw [hf, filter_xor_length_mod_two]
  unfold posPortPar arrCount depCount Drift.arrivals Drift.departures classPhases2
  simp only [ht, ite_true]
  rfl

/-- Local mod-4 congruence at `Q_{t,r}` (Ke §4 / Jillhewar `D_Q ≡ m_v - 2 p_v (mod 4)`). -/
theorem even_layer_mod_four_congr {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    ((classMult P w t r : Int) - (classMult P w t r % 2 : Int) -
      2 * (posPortPar P w t r : Int)) % 4 = 0 := by
  have hp := even_layer_left_mod_two h hd ht r
  omega

/-- Local L14 reduction at `Q_{t,r}`: `p_v * (m_v - 1) ≡ p_v * (D_v + 1) = localCorr (mod 2)`. -/
theorem even_layer_localCorr_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    (posPortPar P w t r * (classMult P w t r - 1)) % 2 = localCorr P w t r := by
  have hp := even_layer_left_mod_two h hd ht r
  unfold localCorr
  simp only [ht, ite_true]
  by_cases hm0 : classMult P w t r = 0
  · have hp0 : posPortPar P w t r = 0 := by rw [hm0] at hp; simpa using hp.symm
    simp [hm0, hp0]
  · have hp_cases : posPortPar P w t r = 0 ∨ posPortPar P w t r = 1 := by omega
    rcases hp_cases with hp0 | hp1
    · simp [hp0]
    · simp only [hp1, Nat.one_mul]
      omega

theorem odd_layer_right_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    ((classMult P w j r + 1) / 2) % 2 = posPortPar P w j r := by
  have hcnt := (h.class_turn_counts (classRep j r)).2.1
  rw [hd] at hcnt
  change ((classPhases2 P w j r).filter (fun i => !w i)).length = (classMult P w j r + 1) / 2 at hcnt
  rw [← hcnt]
  have hf :
      (classPhases2 P w j r).filter (fun i => !w i) =
        (classPhases2 P w j r).filter
          (fun i => xor (decide (inDir w i = .east)) (decide (outDir w i = .north))) := by
    apply List.filter_congr
    intro i hi
    exact odd_layer_right_iff_xor hj hi
  rw [hf, filter_xor_length_mod_two]
  unfold posPortPar arrCount depCount Drift.arrivals Drift.departures classPhases2
  have hne : j % 2 ≠ 0 := by omega
  simp only [hne, ite_false]
  rfl

/-- Local mod-4 congruence at `C_{j,r}` (Ke §4 / Jillhewar `D_C ≡ 2 p_v - m_v (mod 4)`). -/
theorem odd_layer_mod_four_congr {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    ((classMult P w j r : Int) + (classMult P w j r % 2 : Int) -
      2 * (posPortPar P w j r : Int)) % 4 = 0 := by
  have hp := odd_layer_right_mod_two h hd hj r
  omega

/-- Local L14 reduction at `C_{j,r}`:
`binom(m_v, 2) + p_v * (m_v - 1) ≡ D_v * (p_v + 1) = localCorr (mod 2)`. -/
theorem odd_layer_localCorr_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    (classMult P w j r * (classMult P w j r - 1) / 2 +
      posPortPar P w j r * (classMult P w j r - 1)) % 2 = localCorr P w j r := by
  have hp := odd_layer_right_mod_two h hd hj r
  unfold localCorr
  have hne : j % 2 ≠ 0 := by omega
  simp only [hne, ite_false]
  have hc2 := choose2_mod_two (classMult P w j r)
  have hm_mod4 : classMult P w j r % 4 = 0 ∨ classMult P w j r % 4 = 1 ∨
      classMult P w j r % 4 = 2 ∨ classMult P w j r % 4 = 3 := by omega
  rcases hm_mod4 with h0 | h1 | h2 | h3
  · have hp0 : posPortPar P w j r = 0 := by omega
    have h23 : ¬ (classMult P w j r % 4 = 2 ∨ classMult P w j r % 4 = 3) := by omega
    simp only [h23, ite_false] at hc2
    simp only [hp0, Nat.zero_mul, Nat.add_zero]
    have hd0 : classMult P w j r % 2 = 0 := by omega
    simp [hd0, hc2]
  · have hp1 : posPortPar P w j r = 1 := by omega
    have h23 : ¬ (classMult P w j r % 4 = 2 ∨ classMult P w j r % 4 = 3) := by omega
    simp only [h23, ite_false] at hc2
    simp only [hp1, Nat.one_mul]
    omega
  · have hp1 : posPortPar P w j r = 1 := by omega
    have h23 : classMult P w j r % 4 = 2 ∨ classMult P w j r % 4 = 3 := Or.inl h2
    simp only [h23, ite_true] at hc2
    simp only [hp1, Nat.one_mul]
    have hd0 : classMult P w j r % 2 = 0 := by omega
    simp only [hd0, Nat.zero_mul]
    omega
  · have hp0 : posPortPar P w j r = 0 := by omega
    have h23 : classMult P w j r % 4 = 2 ∨ classMult P w j r % 4 = 3 := Or.inr h3
    simp only [h23, ite_true] at hc2
    simp only [hp0, Nat.zero_mul, Nat.add_zero]
    have hd1 : classMult P w j r % 2 = 1 := by omega
    simp only [hd1, Nat.one_mul]
    omega

/-- **L22(3a):** Under `PureOddWake`, the two even-layer classes `Q_{t,false}` and `Q_{t,true}`
on any even layer `t` have equal `posPortPar`, so their local corrections cancel in pairs. -/
theorem pureOdd_posPortPar_even_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {t : Int} (ht : t % 2 = 0) :
    posPortPar P w t false = posPortPar P w t true := by
  have hnF := depCount_eq_arrCount_north h.1 hd (t - 1) false
  have hnT := depCount_eq_arrCount_north h.1 hd (t - 1) true
  rw [show t - 1 + 1 = t by omega] at hnF hnT
  have heF := pureOdd_eCnt_mod_two h hd hpure ht false
  have heT := pureOdd_eCnt_mod_two h hd hpure ht true
  unfold posPortPar
  simp only [ht, ite_true, ← hnF, ← hnT]
  change (nCnt P w (t - 1) false + eCnt P w t false) % 2 =
    (nCnt P w (t - 1) true + eCnt P w t true) % 2
  simp only [Bool.not_false, Bool.not_true] at heF heT
  omega

theorem pureOdd_localCorr_even_pair_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {t : Int} (ht : t % 2 = 0) :
    (localCorr P w t false + localCorr P w t true) % 2 = 0 := by
  have heq := pureOdd_posPortPar_even_eq h hd hpure ht
  have hmF := (pureOddWake_iff_even_classMult_even hd).mp hpure t false ht
  have hmT := (pureOddWake_iff_even_classMult_even hd).mp hpure t true ht
  unfold localCorr
  simp only [ht, ite_true, hmF, hmT, heq]
  omega

/-- **L22(3b):** Under `PureOddWake`, every odd-layer class `C_{j,r}` satisfies `p_v = D_v`,
so its local correction `D_v (p_v + 1) mod 2` vanishes identically. -/
theorem pureOdd_posPortPar_odd_eq_mult {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    posPortPar P w j r = classMult P w j r % 2 := by
  have he_arr := depCount_eq_arrCount_east h.1 hd (j - 1) (!r)
  rw [show j - 1 + 1 = j by omega, Bool.not_not] at he_arr
  have he_mod := pureOdd_eCnt_mod_two h hd hpure (show (j - 1) % 2 = 0 by omega) (!r)
  rw [show j - 1 - 1 = j - 2 by omega, Bool.not_not] at he_mod
  have hD := pureOdd_odd_classMult_mod_two h hd hpure hj r
  unfold posPortPar
  have hne : j % 2 ≠ 0 := by omega
  simp only [hne, ite_false, ← he_arr]
  change (eCnt P w (j - 1) (!r) + nCnt P w j r) % 2 = classMult P w j r % 2
  omega

theorem pureOdd_localCorr_odd_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    {j : Int} (hj : j % 2 = 1) (r : Bool) :
    localCorr P w j r = 0 := by
  have hp := pureOdd_posPortPar_odd_eq_mult h hd hpure hj r
  unfold localCorr
  have hne : j % 2 ≠ 0 := by omega
  simp only [hne, ite_false, hp]
  have hd_cases : classMult P w j r % 2 = 0 ∨ classMult P w j r % 2 = 1 := by omega
  rcases hd_cases with h0 | h1
  · simp [h0]
  · simp [h1]

/-- **L22(3c):** On every layer `t : Int` (even or odd), the sum of the two lane corrections is
`0 (mod 2)`, hence the global local correction `L` over any list of layers vanishes mod 2. -/
theorem pureOdd_localCorr_layer_sum_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    (t : Int) :
    (localCorr P w t false + localCorr P w t true) % 2 = 0 := by
  by_cases ht : t % 2 = 0
  · exact pureOdd_localCorr_even_pair_zero h hd hpure ht
  · have hj : t % 2 = 1 := by omega
    rw [pureOdd_localCorr_odd_zero h hd hpure hj false,
      pureOdd_localCorr_odd_zero h hd hpure hj true]

theorem pureOdd_total_localCorr_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w)
    (ts : List Int) :
    (ts.map (fun t => localCorr P w t false + localCorr P w t true)).sum % 2 = 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht := pureOdd_localCorr_layer_sum_zero h hd hpure t
    omega

/-! ### L24 arithmetic bridge: `4 ∣ P`, `K ≡ 0 (mod 2)`, and `o_r ≡ 2 (mod 4)` -/

private theorem wordPos_fst_parity (w : Nat → Bool) (n : Nat) :
    ((wordPos w n).1 - (((n + 1) / 2 : Nat) : Int)) % 2 = 0 := by
  induction n with
  | zero => simp [wordPos, wordTrace]
  | succ n ih =>
    have hax := wordTrace_axis w n
    have hpos : wordPos w (n + 1) = move (wordPos w n) (turn (w n) (wordTrace w n).2) := rfl
    rw [hpos]
    cases hd' : (wordTrace w n).2 <;> rw [hd'] at hax <;> cases w n <;>
      simp only [Direction.horizontal, turn, Direction.left, Direction.right, move,
        Bool.false_eq_true, ite_true, ite_false] at hax ⊢
    all_goals
      try (have hodd : n % 2 = 1 := of_decide_eq_true hax.symm; omega)
      try (have hev : ¬ (n % 2 = 1) := by
            intro ho; rw [ho] at hax; simp at hax
           omega)

/-- Any consistent word with even horizontal drift (in particular `(2, -2)`) has `4 ∣ P`. -/
theorem period_mod_four_of_driftX_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hx : (wordDrift P w).1 % 2 = 0) :
    P % 4 = 0 := by
  have hp := wordPos_fst_parity w P
  have hev := h.even
  change ((wordDrift P w).1 - (((P + 1) / 2 : Nat) : Int)) % 2 = 0 at hp
  omega

theorem period_mod_four_eq_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    P % 4 = 0 :=
  period_mod_four_of_driftX_even h (by simp [hd])

/-- Total left-turn stable-rank sum `K = ∑_{i < P, w i = true} stableRank P w i`. -/
def leftRankSum (P : Nat) (w : Nat → Bool) : Nat :=
  (((List.range P).filter (fun i => w i)).map (Drift.stableRank P w)).sum

private theorem nat_sum_mod_two_of_all_odd {α : Type} (f : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, f x % 2 = 1) :
    (xs.map f).sum % 2 = xs.length % 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    omega

theorem leftRankSum_mod_two_eq_leftCount {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    leftRankSum P w % 2 = leftCount P w % 2 := by
  unfold leftRankSum leftCount
  apply nat_sum_mod_two_of_all_odd
  intro i hi
  obtain ⟨hiR, hwi⟩ := List.mem_filter.mp hi
  have hcol := Drift.consistentWord_stableRank_color h (List.mem_range.mp hiR)
  rw [hwi] at hcol
  exact of_decide_eq_true hcol.symm

/-- For every `(2, -2)` consistent word, `K = leftRankSum P w ≡ #L ≡ 0 (mod 2)`. -/
theorem leftRankSum_mod_two_eq_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    leftRankSum P w % 2 = 0 := by
  rw [leftRankSum_mod_two_eq_leftCount h]
  exact h.leftCount_even_of_four_dvd (period_mod_four_eq_zero h hd)

/-- Number `o_r` of odd full-translation classes in lane `r : Bool`. -/
def laneOddCount (P : Nat) (w : Nat → Bool) (r : Bool) : Nat :=
  ((oddClassReps P w).filter (fun i => decide (lane (wordPos w i) = r))).length

private theorem int_sum_map_neg_ones {α : Type} (xs : List α) :
    (xs.map (fun _ => (-1 : Int))).sum = -(xs.length : Int) := by
  induction xs with
  | nil => simp
  | cons _ xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Int.natCast_add, Int.natCast_one]
    omega

private theorem int_sum_map_congr' {α : Type} {f g : α → Int} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons,
      h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Under `PureOddWake`, each lane contains `o_r ≡ 2 (mod 4)` odd classes, so
`binom(o_false, 2) + binom(o_true, 2) ≡ 1 + 1 ≡ 0 (mod 2)`. -/
theorem pureOdd_laneOddCount_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) (r : Bool) :
    laneOddCount P w r % 4 = 2 := by
  have ha : (wordDrift P w).1 ≠ 0 := by simp [hd]
  have habs : (wordDrift P w).1.natAbs = 2 := by simp [hd]
  let rn : Nat := if r then 1 else 0
  have hrlt : rn < (wordDrift P w).1.natAbs := by
    rw [habs]; cases r <;> decide
  have hres := h.residue_sum_x_mod_four ha hrlt
  rw [habs] at hres
  have hfilt :
      (oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % ((2 : Nat) : Int) = (rn : Int))) =
        (oddClassReps P w).filter (fun i => decide (lane (wordPos w i) = r)) := by
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    cases r
    · simp only [rn, Bool.false_eq_true, ite_false, Int.natCast_zero, lane_eq_false_iff]; rfl
    · simp only [rn, ite_true, Int.natCast_one, lane_eq_true_iff]; rfl
  rw [hfilt] at hres
  have hneg :
      (((oddClassReps P w).filter (fun i => decide (lane (wordPos w i) = r))).map
        (fun i => checkerSign (wordPos w i))).sum =
      -(laneOddCount P w r : Int) := by
    unfold laneOddCount
    rw [← int_sum_map_neg_ones]
    apply int_sum_map_congr'
    intro i hi
    exact hpure i (List.mem_filter.mp hi).1
  rw [hneg] at hres
  omega

theorem pureOdd_laneOddCount_choose2_sum_mod_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) :
    (laneOddCount P w false * (laneOddCount P w false - 1) / 2 +
      laneOddCount P w true * (laneOddCount P w true - 1) / 2) % 2 = 0 := by
  have h0 := pureOdd_laneOddCount_mod_four h hd hpure false
  have h1 := pureOdd_laneOddCount_mod_four h hd hpure true
  have c0 := choose2_mod_two (laneOddCount P w false)
  have c1 := choose2_mod_two (laneOddCount P w true)
  simp only [h0, true_or, ite_true] at c0
  simp only [h1, true_or, ite_true] at c1
  omega

/-- The finite list of all odd layers between `botLayer P w` and `topLayer P w` (inclusive). -/
def oddLayers (P : Nat) (w : Nat → Bool) : List Int :=
  (List.range ((layerWidth P w / 2).toNat + 1)).map
    (fun k : Nat => botLayer P w + 2 * (k : Int))

private theorem nodup_map_on' {α β : Type} {xs : List α} {f : α → β}
    (hn : xs.Nodup) (hf : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
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

theorem oddLayers_nodup (P : Nat) (w : Nat → Bool) :
    (oddLayers P w).Nodup := by
  unfold oddLayers
  exact nodup_map_on' List.nodup_range (fun _ _ _ _ heq => by omega)

theorem mem_oddLayers {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) {j : Int} :
    j ∈ oddLayers P w ↔ j % 2 = 1 ∧ botLayer P w ≤ j ∧ j ≤ topLayer P w := by
  have hbot := botLayer_odd h hd
  have htop := topLayer_odd h hd
  have hW := layerWidth_ge_two h hd
  unfold oddLayers layerWidth at hW ⊢
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := List.mem_range.mp hk
    omega
  · rintro ⟨hj, hlo, hhi⟩
    refine ⟨((j - botLayer P w) / 2).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

private theorem filter_mod_two_length_eq_sum {α : Type} (f : α → Nat) (xs : List α) :
    (xs.filter (fun x => decide (f x % 2 = 1))).length = (xs.map (fun x => f x % 2)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h1 : f x % 2 = 1
    · simp only [List.filter_cons, h1, decide_true, ite_true, List.length_cons,
        List.map_cons, List.sum_cons, ih]
      omega
    · have h0 : f x % 2 = 0 := by omega
      rw [List.filter_cons, decide_eq_false h1]
      simp only [Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons, h0, ih]
      omega

/-- Under `PureOddWake`, `laneOddCount P w r` equals the sum of `D_{C_{j,r}} = classMult j r mod 2`
over `oddLayers P w`. -/
theorem pureOdd_laneOddCount_eq_oddLayers_sum {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) (r : Bool) :
    laneOddCount P w r = ((oddLayers P w).map (fun j => classMult P w j r % 2)).sum := by
  rw [← filter_mod_two_length_eq_sum]
  let lhs := (oddClassReps P w).filter (fun i => decide (lane (wordPos w i) = r))
  let rhs := (oddLayers P w).filter (fun j => decide (classMult P w j r % 2 = 1))
  have hperm : (lhs.map (fun i => layer (wordPos w i))).Perm rhs := by
    have hndL : (lhs.map (fun i => layer (wordPos w i))).Nodup := by
      apply nodup_map_on' ((oddClassReps_nodup P w).filter _)
      intro i hi j hj hlay
      obtain ⟨hiO, hir⟩ := List.mem_filter.mp hi
      obtain ⟨hjO, hjr⟩ := List.mem_filter.mp hj
      have hsc : Drift.SameClass (wordDrift P w) (wordPos w i) (wordPos w j) := by
        rw [hd, sameClass_two_negTwo_iff]
        exact ⟨hlay, (of_decide_eq_true hir).trans (of_decide_eq_true hjr).symm⟩
      by_cases hij : i = j
      · exact hij
      · exact False.elim (rankZeroReps_not_sameClass h.2.1
          (mem_rankZeroReps.mpr ⟨(mem_oddClassReps.mp hiO).1, (mem_oddClassReps.mp hiO).2.1⟩)
          (mem_rankZeroReps.mpr ⟨(mem_oddClassReps.mp hjO).1, (mem_oddClassReps.mp hjO).2.1⟩)
          hij hsc)
    have hndR : rhs.Nodup := (oddLayers_nodup P w).filter _
    apply (List.perm_ext_iff_of_nodup hndL hndR).mpr
    intro j
    rw [List.mem_map]
    simp only [lhs, rhs, List.mem_filter, decide_eq_true_eq, mem_oddLayers h hd]
    constructor
    · rintro ⟨i, ⟨hiO, hir⟩, rfl⟩
      obtain ⟨hiP, _, hmod⟩ := mem_oddClassReps.mp hiO
      have hchi := hpure i hiO
      rw [checkerSign_eq_neg_one_iff_layer_odd] at hchi
      have hsame : sameClassPhases P w i = classPhases2 P w (layer (wordPos w i)) r := by
        unfold sameClassPhases classPhases2
        rw [hd]
        exact Drift.classPhases_congr P w ((sameClass_two_negTwo_classRep _ _ _).mpr ⟨rfl, hir⟩)
      rw [hsame] at hmod
      exact ⟨⟨hchi, botLayer_le_layer hiP, layer_le_topLayer hiP⟩, hmod⟩
    · rintro ⟨⟨_, _, _⟩, hodd⟩
      have hpos : 0 < (Drift.classPhases (2, -2) P w (classRep j r)).length := by
        unfold classMult classPhases2 at hodd; omega
      obtain ⟨i, hiC, hirank⟩ :=
        Drift.stableRank_surjective_on_class (v := (2, -2)) (c := classRep j r) hd
          drift_two_negTwo_ne_zero hpos
      obtain ⟨hiP, hisc⟩ := Drift.mem_classPhases.mp hiC
      obtain ⟨hli, hri⟩ := (sameClass_two_negTwo_classRep _ _ _).mp hisc
      have hsame : sameClassPhases P w i = classPhases2 P w j r := by
        unfold sameClassPhases classPhases2
        rw [hd]
        exact Drift.classPhases_congr P w hisc
      refine ⟨i, ⟨mem_oddClassReps.mpr ⟨hiP, hirank, ?_⟩, hri⟩, hli⟩
      rw [hsame]
      exact hodd
  have hlen := hperm.length_eq
  simpa only [List.length_map, lhs, rhs, laneOddCount] using hlen

/-- Exact 1D binary run-boundary identity: for any Boolean sequence `b` starting at `b 0 = false`,
the number of transitions `b k ≠ b (k+1)` over `k < m` equals `2 * (#falling edges)` plus `1` if `b m`. -/
private theorem binary_chain_boundary_eq (b : Nat → Bool) (hb0 : b 0 = false) (m : Nat) :
    ((List.range m).map (fun k => if b k != b (k + 1) then (1 : Nat) else 0)).sum =
      2 * ((List.range m).map (fun k => if b k && !b (k + 1) then (1 : Nat) else 0)).sum +
        if b m then 1 else 0 := by
  induction m with
  | zero => simp [hb0]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton, ih]
    cases b m <;> cases b (m + 1) <;> simp <;> omega

/-- **L22/L23 bridge (one-lane chain parity):** Under `PureOddWake`, the gadget-parity sum
`∑_{j ∈ oddLayers} (n_{j,r} + n_{j,r} * n_{j+2,r}) mod 2` equals `o_r / 2 mod 2 = 1` in each lane `r`,
hence the two-lane sum is `0 (mod 2)`. -/
theorem pureOdd_lane_chain_parity_eq_one {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) (r : Bool) :
    ((oddLayers P w).map (fun j =>
      nCnt P w j r % 2 + (nCnt P w j r % 2) * (nCnt P w (j + 2) r % 2))).sum % 2 = 1 := by
  let m : Nat := (layerWidth P w / 2).toNat + 1
  let b : Nat → Bool := fun k =>
    decide (nCnt P w (botLayer P w - 2 + 2 * (k : Int)) r % 2 = 1)
  have hb_eval : ∀ k : Nat, ∀ t : Int, botLayer P w - 2 + 2 * (k : Int) = t →
      b k = decide (nCnt P w t r % 2 = 1) := by
    intro k t ht
    exact congrArg (fun x => decide (nCnt P w x r % 2 = 1)) ht
  have hb0 : b 0 = false := by
    rw [hb_eval 0 (botLayer P w - 2) (by omega)]
    have h0 : nCnt P w (botLayer P w - 2) r = 0 :=
      depCount_eq_zero_of_lt_bot (P := P) (w := w) r .north (by omega)
    exact decide_eq_false (by rw [h0]; omega)
  have hbm : b m = false := by
    have hbot := botLayer_odd h hd
    have htop := topLayer_odd h hd
    have hW := layerWidth_ge_two h hd
    rw [hb_eval m (topLayer P w) (by dsimp [m]; unfold layerWidth at hW ⊢; omega)]
    exact decide_eq_false (by rw [nCnt_topLayer_eq_zero h hd r]; omega)
  have hchain := binary_chain_boundary_eq b hb0 m
  rw [hbm] at hchain
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hchain
  have hbot := botLayer_odd h hd
  have hbdry :
      laneOddCount P w r =
        ((List.range m).map (fun k => if b k != b (k + 1) then (1 : Nat) else 0)).sum := by
    rw [pureOdd_laneOddCount_eq_oddLayers_sum h hd hpure r]
    unfold oddLayers
    rw [List.map_map]
    change ((List.range m).map (fun k : Nat => classMult P w (botLayer P w + 2 * (k : Int)) r % 2)).sum = _
    congr 1
    apply List.map_congr_left
    intro k _
    have hj : (botLayer P w + 2 * (k : Int)) % 2 = 1 := by omega
    rw [pureOdd_odd_classMult_mod_two h hd hpure hj r]
    rw [hb_eval k (botLayer P w + 2 * (k : Int) - 2) (by omega),
      hb_eval (k + 1) (botLayer P w + 2 * (k : Int)) (by omega)]
    by_cases h1 : nCnt P w (botLayer P w + 2 * (k : Int) - 2) r % 2 = 1 <;>
      by_cases h2 : nCnt P w (botLayer P w + 2 * (k : Int)) r % 2 = 1 <;>
      simp [h1, h2] <;> omega
  have hruns :
      ((oddLayers P w).map (fun j =>
        nCnt P w j r % 2 + (nCnt P w j r % 2) * (nCnt P w (j + 2) r % 2))).sum % 2 =
      ((List.range m).map (fun k => if b k && !b (k + 1) then (1 : Nat) else 0)).sum % 2 := by
    have hshift :
        ((List.range m).map (fun k => if b k && !b (k + 1) then (1 : Nat) else 0)).sum =
        ((List.range m).map (fun k => if b (k + 1) && !b (k + 2) then (1 : Nat) else 0)).sum := by
      have h1 :
          ((List.range (m + 1)).map (fun k => if b k && !b (k + 1) then (1 : Nat) else 0)).sum =
            ((List.range m).map (fun k => if b k && !b (k + 1) then (1 : Nat) else 0)).sum := by
        rw [List.range_succ, List.map_append, List.sum_append]
        simp [hbm]
      have h2 :
          ((List.range (m + 1)).map (fun k => if b k && !b (k + 1) then (1 : Nat) else 0)).sum =
            ((List.range m).map (fun k => if b (k + 1) && !b (k + 2) then (1 : Nat) else 0)).sum := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
        simp [hb0, Function.comp_def]
      omega
    rw [hshift]
    unfold oddLayers
    rw [List.map_map]
    change ((List.range m).map _).sum % 2 = _
    have hmod_congr : ∀ (xs : List Nat) (f g : Nat → Nat),
        (∀ k ∈ xs, f k % 2 = g k % 2) → (xs.map f).sum % 2 = (xs.map g).sum % 2 := by
      intro xs f g hfg
      induction xs with
      | nil => simp
      | cons a xs ixs =>
        simp only [List.map_cons, List.sum_cons]
        have ha := hfg a (by simp)
        have hxs := ixs (fun y hy => hfg y (by simp [hy]))
        omega
    apply hmod_congr
    intro k _
    rw [hb_eval (k + 1) (botLayer P w + 2 * (k : Int)) (by omega),
      hb_eval (k + 2) (botLayer P w + 2 * (k : Int) + 2) (by omega)]
    by_cases h1 : nCnt P w (botLayer P w + 2 * (k : Int)) r % 2 = 1 <;>
      by_cases h2 : nCnt P w (botLayer P w + 2 * (k : Int) + 2) r % 2 = 1
    · simp [h1, h2]
    · have h20 : nCnt P w (botLayer P w + 2 * (k : Int) + 2) r % 2 = 0 := by omega
      simp [h1, h20]
    · have h10 : nCnt P w (botLayer P w + 2 * (k : Int)) r % 2 = 0 := by omega
      simp [h2, h10]
    · have h10 : nCnt P w (botLayer P w + 2 * (k : Int)) r % 2 = 0 := by omega
      have h20 : nCnt P w (botLayer P w + 2 * (k : Int) + 2) r % 2 = 0 := by omega
      simp [h10, h20]
  have ho := pureOdd_laneOddCount_mod_four h hd hpure r
  rw [hbdry, hchain] at ho
  rw [hruns]
  omega

theorem pureOdd_twoLane_chain_parity_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) :
    (((oddLayers P w).map (fun j =>
      nCnt P w j false % 2 + (nCnt P w j false % 2) * (nCnt P w (j + 2) false % 2))).sum +
     ((oddLayers P w).map (fun j =>
      nCnt P w j true % 2 + (nCnt P w j true % 2) * (nCnt P w (j + 2) true % 2))).sum) % 2 = 0 := by
  have hF := pureOdd_lane_chain_parity_eq_one h hd hpure false
  have hT := pureOdd_lane_chain_parity_eq_one h hd hpure true
  omega

/-! ## 4. Non-vacuity sanity check on the rotated standard 104-step highway (`drift = (2, -2)`) -/

/-- Shifting the standard 104-step highway (`certifiedColor`, drift `(-2, -2)`) by phase `7`
(where the ant faces `.east`) rotates its full drift to `(2, -2)` while preserving consistency
and growth `g = 12`. -/
def stdHighwaySE (i : Nat) : Bool :=
  repeatWord 104 certifiedColor (7 + i)

theorem stdHighwaySE_consistent : ConsistentWord 104 stdHighwaySE :=
  (standard_word_consistent.growth_shift 7).1

theorem stdHighwaySE_growth : wordGrowth 104 stdHighwaySE = 12 := by
  have hg := (standard_word_consistent.growth_shift 7).2.1
  rw [standard_word_growth] at hg
  exact hg

theorem stdHighwaySE_drift : wordDrift 104 stdHighwaySE = (2, -2) := by
  have hd := (standard_word_consistent.growth_shift 7).2.2
  have hdir : (wordTrace (repeatWord 104 certifiedColor) 7).2 = .east := by decide
  rw [hdir, Drift.standard_word_drift] at hd
  exact hd

private def traceLayersFrom (w : Nat → Bool) : Nat → Nat → Point × Direction → List Int
  | 0, _, _ => []
  | n + 1, k, st =>
      layer st.1 :: traceLayersFrom w n (k + 1) (move st.1 (turn (w k) st.2), turn (w k) st.2)

private theorem traceLayersFrom_eq_map_range (w : Nat → Bool) (n k : Nat) :
    traceLayersFrom w n k (wordTrace w k) =
      (List.range n).map (fun i => layer (wordPos w (k + i))) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [traceLayersFrom, wordPos, Nat.add_zero, Function.comp_def]
    have hstep : (move (wordTrace w k).1 (turn (w k) (wordTrace w k).2),
        turn (w k) (wordTrace w k).2) = wordTrace w (k + 1) := rfl
    rw [hstep, ih (k + 1)]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [show k + 1 + i = k + (i + 1) by omega]
    rfl

theorem stdHighwaySE_topLayer : topLayer 104 stdHighwaySE = 9 := by
  unfold topLayer
  have h := traceLayersFrom_eq_map_range stdHighwaySE 104 0
  simp only [Nat.zero_add] at h
  rw [← h]
  decide +kernel

theorem stdHighwaySE_botLayer : botLayer 104 stdHighwaySE = -1 := by
  unfold botLayer
  have h := traceLayersFrom_eq_map_range stdHighwaySE 104 0
  simp only [Nat.zero_add] at h
  rw [← h]
  decide +kernel

theorem stdHighwaySE_layerWidth : layerWidth 104 stdHighwaySE = 10 := by
  unfold layerWidth
  rw [stdHighwaySE_topLayer, stdHighwaySE_botLayer]
  decide

theorem stdHighwaySE_topPhases : layerPhases 104 stdHighwaySE 9 = [41, 59] := by
  decide +kernel

theorem stdHighwaySE_botPhases : layerPhases 104 stdHighwaySE (-1) = [89, 103] := by
  decide +kernel

/-- Non-vacuity check: the rotated standard 104-step highway (`stdHighwaySE`, drift `(2, -2)`,
growth `12`, width `10`) satisfies all headline L21 and L22/L24 hypotheses and conclusions.
Its top extremal layer `9` has singleton classes at phases `41` (`(7, 2)`, lane `true`) and
`59` (`(6, 3)`, lane `false`), and its bottom extremal layer `-1` has singleton classes at
phases `89` (`(1, -2)`, lane `true`) and `103` (`(2, -3)`, lane `false`). -/
theorem stdHighwaySE_nonvacuity :
    ConsistentWord 104 stdHighwaySE ∧
    wordDrift 104 stdHighwaySE = (2, -2) ∧
    wordGrowth 104 stdHighwaySE = 12 ∧
    topLayer 104 stdHighwaySE = 9 ∧
    botLayer 104 stdHighwaySE = -1 ∧
    layerWidth 104 stdHighwaySE = 10 ∧
    (∀ i, i < 104 → layer (wordPos stdHighwaySE i) = 9 →
      Drift.stableRank 104 stdHighwaySE i = 0 ∧
      stdHighwaySE i = false ∧
      inDir stdHighwaySE i = .east ∧
      outDir stdHighwaySE i = .south ∧
      i ∈ oddClassReps 104 stdHighwaySE ∧
      checkerSign (wordPos stdHighwaySE i) = -1) ∧
    (∀ i, i < 104 → layer (wordPos stdHighwaySE i) = -1 →
      Drift.stableRank 104 stdHighwaySE i = 0 ∧
      stdHighwaySE i = false ∧
      inDir stdHighwaySE i = .west ∧
      outDir stdHighwaySE i = .north ∧
      i ∈ oddClassReps 104 stdHighwaySE ∧
      checkerSign (wordPos stdHighwaySE i) = -1) ∧
    2 ≤ ((oddClassReps 104 stdHighwaySE).filter
      (fun i => decide (checkerSign (wordPos stdHighwaySE i) = -1))).length ∧
    ¬ (∀ i ∈ oddClassReps 104 stdHighwaySE, checkerSign (wordPos stdHighwaySE i) = 1) ∧
    leftRankSum 104 stdHighwaySE % 2 = 0 := by
  refine ⟨stdHighwaySE_consistent, stdHighwaySE_drift, stdHighwaySE_growth,
    stdHighwaySE_topLayer, stdHighwaySE_botLayer, stdHighwaySE_layerWidth, ?_, ?_,
    two_le_neg_oddClassReps stdHighwaySE_consistent stdHighwaySE_drift,
    not_all_oddClassReps_pos stdHighwaySE_consistent stdHighwaySE_drift,
    leftRankSum_mod_two_eq_zero stdHighwaySE_consistent stdHighwaySE_drift⟩
  · intro i hi htop
    have hr := topLayer_phase_rigid stdHighwaySE_consistent stdHighwaySE_drift hi
      (by rw [stdHighwaySE_topLayer]; exact htop)
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2⟩
  · intro i hi hbot
    have hr := botLayer_phase_rigid stdHighwaySE_consistent stdHighwaySE_drift hi
      (by rw [stdHighwaySE_botLayer]; exact hbot)
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2⟩

end TwoCellDiagonal
end LangtonsAnt
