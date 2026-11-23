import WidthLemmas

/-!
Finite cut sums for the actual word geometry, in the north-facing word frame.
All sums count phase occurrences, including edges that cross the period seam.
The proofs below use cyclic incidence, so they do not require a strict bound
on excursion length and retain the full-period case.
-/

namespace LangtonsAnt.WidthCutSum

open TwoCellDiagonal WidthLemmas

private theorem sum_congr {A : Type} {xs : List A} {f g : A -> Int}
    (h : forall x, x ∈ xs -> f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  exact congrArg List.sum (List.map_congr_left h)

private theorem sum_add {A : Type} (xs : List A) (f g : A -> Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_sub {A : Type} (xs : List A) (f g : A -> Int) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_mul {A : Type} (xs : List A) (c : Int) (f : A -> Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Int.mul_add]

private theorem sum_zero {A : Type} (xs : List A) :
    (xs.map (fun _ => (0 : Int))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_filter {A : Type} (xs : List A) (p : A -> Bool) (f : A -> Int) :
    ((xs.filter p).map f).sum = (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

private theorem sum_indicator {A : Type} (xs : List A) (p : A -> Bool) :
    (xs.map (fun x => if p x then (1 : Int) else 0)).sum = (xs.filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih] <;> omega

private theorem sum_next (P : Nat) (f : Nat -> Int) :
    ((List.range P).map (fun i => f (nextPhase P i))).sum =
      ((List.range P).map f).sum := by
  cases P with
  | zero => simp
  | succ n =>
    conv => lhs; rw [List.range_succ, List.map_append, List.sum_append]
    have he : ((List.range n).map (fun i => f (nextPhase (n + 1) i))).sum =
        ((List.range n).map (fun i => f (i + 1))).sum := by
      apply sum_congr
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [nextPhase_eq_ite (by omega), ite_eq_left (by omega)]
    rw [he]
    have hn : nextPhase (n + 1) n = 0 := by simp [nextPhase]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      List.map_nil, List.sum_nil, Nat.succ_eq_add_one, Int.add_zero, hn]
    omega

private theorem cyclic_incidence (P : Nat) (a f : Nat -> Int) :
    ((List.range P).map (fun i => a i * (f (nextPhase P i) - f i))).sum =
      ((List.range P).map (fun i => (a (prevPhase P i) - a i) * f i)).sum := by
  have he : ((List.range P).map (fun i => a i * f (nextPhase P i))).sum =
      ((List.range P).map (fun i => a (prevPhase P i) * f i)).sum := by
    rw [← sum_next P (fun i => a (prevPhase P i) * f i)]
    apply sum_congr
    intro i hi
    rw [prevPhase_nextPhase (List.mem_range.mp hi)]
  simp only [Int.mul_sub, Int.sub_mul, sum_sub]
  rw [he]

/-- The lower layer of the actual edge departing at phase `i`. -/
def edgeCut (w : Nat -> Bool) (i : Nat) : Int :=
  if beta w i then layer (wordPos w i) else layer (wordPos w i) - 1

/-- Indicator of an edge on or above cut `t`, counted once by its departure phase. -/
def upperWeight (w : Nat -> Bool) (t : Int) (i : Nat) : Int :=
  if t <= edgeCut w i then 1 else 0

/-- Horizontal displacement of one physical step; no seam correction is dropped. -/
def stepX (w : Nat -> Bool) (i : Nat) : Int :=
  (move (wordPos w i) (outDir w i)).1 - (wordPos w i).1

/-- Boundary time with the single common `eta` origin for both lanes. -/
def boundaryTime (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  classBoundaryTime P w t false + classBoundaryTime P w t true

theorem edgeCut_eq_min {P i : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (hi : i < P) :
    edgeCut w i = min (layer (wordPos w i)) (layer (wordPos w (nextPhase P i))) := by
  rw [layer_wordPos_nextPhase_of_layer_zero hlv hi]
  cases hd : outDir w i <;> simp [edgeCut, beta, hd, layerDelta] <;> omega

/-- Pointwise endpoint cancellation. At a splice `alpha = beta = true`,
the incoming and outgoing upper-edge incidences cancel, including at the seam. -/
theorem upper_incidence {P i : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hi : i < P) (t : Int) :
    upperWeight w t (prevPhase P i) - upperWeight w t i =
      if layer (wordPos w i) = t then throughCharge w i else 0 := by
  have hp := layer_wordPos_prevPhase_of_layer_zero hh hlv hi
  have ho := outDir_prevPhase hh hi
  unfold throughCharge upperWeight edgeCut alpha beta
  rw [ho]
  cases hin : inDir w i <;> cases hout : outDir w i <;>
    simp_all [layerDelta] <;> omega

private theorem class_sum (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool)
    (f : Nat -> Int) :
    ((classPhases2 P w t r).map f).sum =
      ((List.range P).map (fun i =>
        if layer (wordPos w i) = t ∧ lane (wordPos w i) = r then f i else 0)).sum := by
  unfold classPhases2 Drift.classPhases
  rw [sum_filter]
  apply sum_congr
  intro i _
  simp only [sameClass_two_negTwo_classRep, decide_eq_true_eq]

/-- The two real translation classes partition all occurrences of layer `t`. -/
theorem two_lane_sum (P : Nat) (w : Nat -> Bool) (t : Int) (f : Nat -> Int) :
    ((classPhases2 P w t false).map f).sum +
        ((classPhases2 P w t true).map f).sum =
      ((List.range P).map (fun i => if layer (wordPos w i) = t then f i else 0)).sum := by
  rw [class_sum, class_sum, ← sum_add]
  apply sum_congr
  intro i _
  cases lane (wordPos w i) <;> by_cases ht : layer (wordPos w i) = t <;>
    simp [ht]

/-- Exact endpoint cancellation, as a finite sum over all upper-region edges.
This is a cyclic discrete divergence theorem, with no excursion-length premise. -/
theorem boundaryTime_eq_upper_eta {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    boundaryTime P w t =
      ((List.range P).map (fun i => upperWeight w t i *
        (eta P w (nextPhase P i) - eta P w i))).sum := by
  unfold boundaryTime classBoundaryTime
  rw [two_lane_sum, cyclic_incidence]
  apply sum_congr
  intro i hi
  rw [upper_incidence hh hlv (List.mem_range.mp hi)]
  split <;> simp

/-- The paper's `Tdown` and `Tup` are actual through events at the cut.
Both bounce types contribute zero, without assigning independent lane origins. -/
theorem boundaryTime_eq_through_sums (P : Nat) (w : Nat -> Bool) (t : Int) :
    boundaryTime P w t =
      (((List.range P).filter (fun i => decide (layer (wordPos w i) = t) &&
        alpha w i && !(beta w i))).map (eta P w)).sum -
      (((List.range P).filter (fun i => decide (layer (wordPos w i) = t) &&
        !(alpha w i) && beta w i)).map (eta P w)).sum := by
  unfold boundaryTime classBoundaryTime
  rw [two_lane_sum, sum_filter, sum_filter, ← sum_sub]
  apply sum_congr
  intro i _
  by_cases ht : layer (wordPos w i) = t <;>
    cases ha : alpha w i <;> cases hb : beta w i <;>
    simp [throughCharge, ht, ha, hb]

/-- The single-edge version of the common-time identity, valid at the seam. -/
theorem eta_next_difference {P i : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (2, -2)) (hi : i < P) :
    eta P w (nextPhase P i) - eta P w i = 2 - (P : Int) * stepX w i := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i 1
  have h0 : p.phase 0 = i := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have h1 : p.phase 1 = nextPhase P i := rfl
  have he := path_eta_difference p hd
  have hs := p.pos_step (w := w) (r := 0) (by decide)
  have hx : (p.pos w 1).1 - (p.pos w 0).1 = stepX w i := by
    rw [hs, h0]
    change (move (p.pos w 0) (outDir w i)).1 - (p.pos w 0).1 = _
    cases ho : outDir w i <;> simp [stepX, ho, move] <;> omega
  simpa only [h0, h1, hx, Int.natCast_one, Int.mul_one] using he

/-- The number of upper-region edge occurrences, expressed as an integer. -/
def upperLength (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  ((List.range P).map (upperWeight w t)).sum

/-- Signed horizontal transport over exactly the same edge occurrences. -/
def upperTransport (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  ((List.range P).map (fun i => upperWeight w t i * stepX w i)).sum

/-- The middle equality in (36.1), stated directly for the actual upper edges. -/
theorem boundaryTime_eq_length_transport {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    boundaryTime P w t = 2 * upperLength P w t - (P : Int) * upperTransport P w t := by
  rw [boundaryTime_eq_upper_eta h.1 (by rw [hd]; rfl)]
  calc
    _ = ((List.range P).map (fun i =>
        2 * upperWeight w t i - (P : Int) * (upperWeight w t i * stepX w i))).sum := by
      apply sum_congr
      intro i hi
      rw [eta_next_difference hd (List.mem_range.mp hi), Int.mul_sub]
      rw [Int.mul_comm (upperWeight w t i) 2, Int.mul_left_comm]
    _ = _ := by rw [sum_sub, sum_mul, sum_mul]; rfl

/-- Upward crossing occurrences of the cut from `t` to `t+1`. -/
def cutFlow (P : Nat) (w : Nat -> Bool) (t : Int) : Nat :=
  eCnt P w t false + nCnt P w t false + eCnt P w t true + nCnt P w t true

/-- Downward crossing occurrences of the same cut, using the actual departure ports. -/
def cutDownFlow (P : Nat) (w : Nat -> Bool) (t : Int) : Nat :=
  sCnt P w (t + 1) false + wCnt P w (t + 1) false +
    sCnt P w (t + 1) true + wCnt P w (t + 1) true

private def upWeight (w : Nat -> Bool) (t : Int) (i : Nat) : Int :=
  if layer (wordPos w i) = t then if beta w i then 1 else 0 else 0

private def downWeight (w : Nat -> Bool) (t : Int) (i : Nat) : Int :=
  if layer (wordPos w i) = t + 1 then if beta w i then 0 else 1 else 0

private theorem depCount_sum (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool)
    (d : Direction) :
    (depCount P w t r d : Int) =
      ((classPhases2 P w t r).map (fun i => if outDir w i = d then 1 else 0)).sum := by
  change (((classPhases2 P w t r).filter (fun i => decide (outDir w i = d))).length : Int) = _
  rw [← sum_indicator]
  apply sum_congr
  intro i _
  simp

private theorem sum_upWeight (P : Nat) (w : Nat -> Bool) (t : Int) :
    ((List.range P).map (upWeight w t)).sum = cutFlow P w t := by
  have hl (r : Bool) : (eCnt P w t r : Int) + (nCnt P w t r : Int) =
      ((classPhases2 P w t r).map (fun i => if beta w i then 1 else 0)).sum := by
    rw [depCount_sum, depCount_sum, ← sum_add]
    apply sum_congr
    intro i _
    cases ho : outDir w i <;> simp [beta, ho]
  have hs := two_lane_sum P w t (fun i => if beta w i then 1 else 0)
  rw [← hl false, ← hl true] at hs
  unfold cutFlow upWeight
  simp only [Int.natCast_add]
  omega

private theorem sum_downWeight (P : Nat) (w : Nat -> Bool) (t : Int) :
    ((List.range P).map (downWeight w t)).sum = cutDownFlow P w t := by
  have hl (r : Bool) : (sCnt P w (t + 1) r : Int) + (wCnt P w (t + 1) r : Int) =
      ((classPhases2 P w (t + 1) r).map (fun i => if beta w i then 0 else 1)).sum := by
    rw [depCount_sum, depCount_sum, ← sum_add]
    apply sum_congr
    intro i _
    cases ho : outDir w i <;> simp [beta, ho]
  have hs := two_lane_sum P w (t + 1) (fun i => if beta w i then 0 else 1)
  rw [← hl false, ← hl true] at hs
  unfold cutDownFlow downWeight
  simp only [Int.natCast_add]
  omega

/-- Every cut has equally many upward and downward crossings over the full phase cycle. -/
theorem cutFlow_eq_cutDownFlow {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    cutFlow P w t = cutDownFlow P w t := by
  let v : Nat -> Int := fun i => if t < layer (wordPos w i) then 1 else 0
  have hs : ((List.range P).map (fun i => v (nextPhase P i) - v i)).sum = 0 := by
    rw [sum_sub, sum_next, Int.sub_self]
  have he : ((List.range P).map (fun i => v (nextPhase P i) - v i)).sum =
      ((List.range P).map (fun i => upWeight w t i - downWeight w t i)).sum := by
    apply sum_congr
    intro i hi
    have hn := layer_wordPos_nextPhase_of_layer_zero hlv (List.mem_range.mp hi)
    dsimp [v]
    rw [hn]
    cases ho : outDir w i <;>
      simp [upWeight, downWeight, beta, ho, layerDelta] <;> omega
  rw [he, sum_sub, sum_upWeight, sum_downWeight] at hs
  omega

/-- The integer sign `(-1)^t` for the north-facing word frame (`sigma = +1`). -/
def cutSign (t : Int) : Int := if t % 2 = 0 then 1 else -1

private theorem outgoing_axis (w : Nat -> Bool) (i : Nat) :
    (outDir w i).horizontal = decide (layer (wordPos w i) % 2 = 0) := by
  have hi := inDir_horizontal_eq w i
  unfold outDir
  cases hd : inDir w i <;> cases w i <;>
    simp_all [turn, Direction.right, Direction.left, Direction.horizontal] <;> omega

private theorem cut_stepX (w : Nat -> Bool) (t : Int) (i : Nat) :
    (if edgeCut w i = t then (1 : Int) else 0) * stepX w i =
      if t % 2 = 0 then upWeight w t i else - downWeight w t i := by
  have ha := outgoing_axis w i
  cases ho : outDir w i <;>
    simp [edgeCut, stepX, beta, upWeight, downWeight, ho, move,
      Direction.horizontal] at ha ⊢ <;> omega

/-- Exact crossing count at one cut: every upward and downward edge occurs once. -/
theorem cut_edge_count {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    ((List.range P).map (fun i => if edgeCut w i = t then (1 : Int) else 0)).sum =
      2 * (cutFlow P w t : Int) := by
  have he : ((List.range P).map (fun i => if edgeCut w i = t then (1 : Int) else 0)).sum =
      ((List.range P).map (fun i => upWeight w t i + downWeight w t i)).sum := by
    apply sum_congr
    intro i _
    cases hb : beta w i <;> simp [edgeCut, upWeight, downWeight, hb] <;> omega
  rw [he, sum_add, sum_upWeight, sum_downWeight, ← cutFlow_eq_cutDownFlow hlv]
  omega

/-- Horizontal crossing transport is signed; it is negative at odd cuts. -/
theorem cut_edge_transport {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    ((List.range P).map (fun i =>
      (if edgeCut w i = t then (1 : Int) else 0) * stepX w i)).sum =
      cutSign t * (cutFlow P w t : Int) := by
  have he := sum_congr (xs := List.range P) (fun i _ => cut_stepX w t i)
  rw [he]
  by_cases ht : t % 2 = 0
  · simp only [ht, ite_true, cutSign, Int.one_mul]
    exact sum_upWeight P w t
  · simp only [ht, ite_false, cutSign]
    have hn : ((List.range P).map (fun i => -downWeight w t i)).sum =
        -((List.range P).map (downWeight w t)).sum := by
      simpa only [Int.neg_one_mul] using sum_mul (List.range P) (-1) (downWeight w t)
    rw [hn, sum_downWeight, ← cutFlow_eq_cutDownFlow hlv, Int.neg_one_mul]

private theorem upperWeight_step (w : Nat -> Bool) (t : Int) (i : Nat) :
    upperWeight w t i = (if edgeCut w i = t then (1 : Int) else 0) +
      upperWeight w (t + 1) i := by
  unfold upperWeight
  omega

theorem upperLength_step {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    upperLength P w t = 2 * (cutFlow P w t : Int) + upperLength P w (t + 1) := by
  unfold upperLength
  rw [sum_congr (fun i _ => upperWeight_step w t i), sum_add, cut_edge_count hlv]

theorem upperTransport_step {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    upperTransport P w t = cutSign t * (cutFlow P w t : Int) +
      upperTransport P w (t + 1) := by
  unfold upperTransport
  have he := sum_congr (xs := List.range P) (fun i _ =>
    congrArg (fun z => z * stepX w i) (upperWeight_step w t i))
  rw [he]
  simp only [Int.add_mul, sum_add, cut_edge_transport hlv]

theorem edgeCut_lt_top {P i : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (hi : i < P) :
    edgeCut w i < topLayer P w := by
  have hc := layer_le_topLayer (w := w) hi
  have hn := layer_le_topLayer (w := w) (nextPhase_lt (P := P) (i := i) (by omega))
  rw [layer_wordPos_nextPhase_of_layer_zero hlv hi] at hn
  cases ho : outDir w i <;> simp [edgeCut, beta, ho, layerDelta] at hn ⊢ <;> omega

/-- This proves the support cutoff used by `sumAbove`, rather than assuming it. -/
theorem cutFlow_eq_zero_of_top_le {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) {t : Int} (ht : topLayer P w <= t) :
    cutFlow P w t = 0 := by
  have hc := cut_edge_count hlv t
  have he : ((List.range P).map (fun i => if edgeCut w i = t then (1 : Int) else 0)).sum =
      ((List.range P).map (fun _ => (0 : Int))).sum := by
    apply sum_congr
    intro i hi
    have hb := edgeCut_lt_top hlv (List.mem_range.mp hi)
    simp [show edgeCut w i ≠ t by omega]
  rw [he, sum_zero] at hc
  omega

theorem cutFlow_eq_zero_of_lt_bot {P : Nat} {w : Nat -> Bool}
    {t : Int} (ht : t < botLayer P w) : cutFlow P w t = 0 := by
  have h0 := classPhases2_eq_nil_of_lt_bot (P := P) (w := w) false ht
  have h1 := classPhases2_eq_nil_of_lt_bot (P := P) (w := w) true ht
  change (List.filter _ (classPhases2 P w t false)).length +
    (List.filter _ (classPhases2 P w t false)).length +
    (List.filter _ (classPhases2 P w t true)).length +
    (List.filter _ (classPhases2 P w t true)).length = 0
  rw [h0, h1]
  rfl

theorem upperLength_eq_zero_of_top_le {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) {t : Int} (ht : topLayer P w <= t) :
    upperLength P w t = 0 := by
  have he : ((List.range P).map (upperWeight w t)).sum =
      ((List.range P).map (fun _ => (0 : Int))).sum := by
    apply sum_congr
    intro i hi
    have hb := edgeCut_lt_top hlv (List.mem_range.mp hi)
    simp [upperWeight, show ¬ t <= edgeCut w i by omega]
  unfold upperLength
  rw [he, sum_zero]

theorem upperTransport_eq_zero_of_top_le {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) {t : Int} (ht : topLayer P w <= t) :
    upperTransport P w t = 0 := by
  have he : ((List.range P).map (fun i => upperWeight w t i * stepX w i)).sum =
      ((List.range P).map (fun _ => (0 : Int))).sum := by
    apply sum_congr
    intro i hi
    have hb := edgeCut_lt_top hlv (List.mem_range.mp hi)
    simp [upperWeight, show ¬ t <= edgeCut w i by omega]
  unfold upperTransport
  rw [he, sum_zero]

/-- Finite notation for `sum_(s >= t)`, with zero support at and above `topLayer`.
The range is empty when the requested lower cut lies above the path. -/
def sumAbove (P : Nat) (w : Nat -> Bool) (t : Int) (f : Int -> Int) : Int :=
  ((List.range (topLayer P w - t).toNat).map (fun k : Nat => f (t + (k : Int)))).sum

private theorem telescope (a g : Int -> Int) (h : forall t, g t = a t + g (t + 1))
    (t : Int) (n : Nat) :
    g t = ((List.range n).map (fun k : Nat => a (t + (k : Int)))).sum + g (t + (n : Int)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton, Int.natCast_add, Int.natCast_one]
    rw [h (t + (n : Int))] at ih
    rw [Int.add_assoc t (n : Int) 1] at ih
    omega

theorem upperLength_eq_twice_sum_cutFlow {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    upperLength P w t = 2 * sumAbove P w t (fun s => (cutFlow P w s : Int)) := by
  have he := telescope (fun s => 2 * (cutFlow P w s : Int)) (upperLength P w)
    (upperLength_step hlv) t (topLayer P w - t).toNat
  rw [upperLength_eq_zero_of_top_le hlv
    (t := t + ((topLayer P w - t).toNat : Int)) (by omega), Int.add_zero, sum_mul] at he
  exact he

theorem upperTransport_eq_signed_sum_cutFlow {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    upperTransport P w t = sumAbove P w t (fun s => cutSign s * (cutFlow P w s : Int)) := by
  have he := telescope (fun s => cutSign s * (cutFlow P w s : Int)) (upperTransport P w)
    (upperTransport_step hlv) t (topLayer P w - t).toNat
  rw [upperTransport_eq_zero_of_top_le hlv
    (t := t + ((topLayer P w - t).toNat : Int)) (by omega), Int.add_zero] at he
  exact he

/-- Round 36, equation (36.1), in the repository's actual north-facing word frame.
The coefficient `sigma` is `+1` in this frame. No positivity of the signed sum,
same-lane condition, short-excursion condition, or unverified covering is assumed. -/
theorem boundaryTime_eq_cut_sums {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    boundaryTime P w t =
      4 * sumAbove P w t (fun s => (cutFlow P w s : Int)) -
        (P : Int) * sumAbove P w t (fun s => cutSign s * (cutFlow P w s : Int)) := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; rfl
  rw [boundaryTime_eq_length_transport h hd, upperLength_eq_twice_sum_cutFlow hlv,
    upperTransport_eq_signed_sum_cutFlow hlv]
  omega

/-- `upperLength` really counts the selected phase occurrences. -/
theorem upperLength_eq_count (P : Nat) (w : Nat -> Bool) (t : Int) :
    upperLength P w t =
      (((List.range P).filter (fun i => decide (t <= edgeCut w i))).length : Int) := by
  unfold upperLength upperWeight
  have he := sum_indicator (List.range P) (fun i => decide (t <= edgeCut w i))
  simpa using he

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Kernel-checked numerical witnesses: the signed transport changes sign. -/
theorem stdHighwaySE_cut_data :
    upperTransport 104 stdHighwaySE 4 = 2 ∧
    upperTransport 104 stdHighwaySE 5 = -7 ∧
    upperLength 104 stdHighwaySE (-1) = 104 ∧
    upperTransport 104 stdHighwaySE (-1) = 2 := by
  decide +kernel

/-- A real consistent word instantiates the full identity, including negative transport. -/
theorem stdHighwaySE_nonvacuous :
    ConsistentWord 104 stdHighwaySE ∧ wordDrift 104 stdHighwaySE = (2, -2) ∧
    boundaryTime 104 stdHighwaySE 5 =
      4 * sumAbove 104 stdHighwaySE 5 (fun s => (cutFlow 104 stdHighwaySE s : Int)) + 728 := by
  have hs := boundaryTime_eq_cut_sums stdHighwaySE_consistent stdHighwaySE_drift 5
  have ht := upperTransport_eq_signed_sum_cutFlow
    (P := 104) (w := stdHighwaySE) (by rw [stdHighwaySE_drift]; rfl) 5
  have hv := stdHighwaySE_cut_data.2.1
  refine ⟨stdHighwaySE_consistent, stdHighwaySE_drift, ?_⟩
  omega

end LangtonsAnt.WidthCutSum
