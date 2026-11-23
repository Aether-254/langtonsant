import WidthCutSum

/-!
Actual upper excursions, endpoint defects, and their moment identities.
Source: research/persist-A-width-2026-11-22.md, rounds 33--35 and the
round-40 correction. All counts refer to phase occurrences of the word.

Upper excursions run from an upward departure at layer t to the first return
to that layer. A B event joins two excursions; its two incidences are retained.
Lengths lie in 1,...,P, and all physical endpoints retain the period carry.
The edge-occurrence covering and signed run transport require botLayer <= t:
below the entire path there are no boundary excursions, but all edges are upper.
The defect and moment theorems do not need this additional support condition.
-/

namespace LangtonsAnt.WidthDefects

open TwoCellDiagonal WidthLemmas WidthCutSum

private theorem sum_congr {A : Type} {xs : List A} {f g : A -> Int}
    (h : forall x, x ∈ xs -> f x = g x) :
    (xs.map f).sum = (xs.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

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

private theorem sum_indicator {A : Type} (xs : List A) (p : A -> Bool) :
    (xs.map (fun x => if p x then (1 : Int) else 0)).sum =
      (xs.filter p).length := by
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

private theorem sum_prev (P : Nat) (f : Nat -> Int) :
    ((List.range P).map (fun i => f (prevPhase P i))).sum =
      ((List.range P).map f).sum := by
  rw [<- sum_next P (fun i => f (prevPhase P i))]
  apply sum_congr
  intro i hi
  rw [prevPhase_nextPhase (List.mem_range.mp hi)]

/-- Counts actual visits with specified incoming/outgoing upper-port bits.
`true,true` is the upper bounce B; `false,true` is the upward through event. -/
def eventCount (P : Nat) (w : Nat -> Bool) (t : Int) (a b : Bool) : Nat :=
  ((List.range P).filter (fun i => decide (layer (wordPos w i) = t) &&
    decide (alpha w i = a) && decide (beta w i = b))).length

abbrev bounceCount (P : Nat) (w : Nat -> Bool) (t : Int) : Nat :=
  eventCount P w t true true

abbrev throughCount (P : Nat) (w : Nat -> Bool) (t : Int) : Nat :=
  eventCount P w t false true

/-- The boundary-event defect. Its run-count interpretation is a separate obligation. -/
def eventDefect (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  (bounceCount P w t : Int) - (throughCount P w t : Int)

/-- The signed wake charge A in the original north-facing frame. -/
def wakeCharge (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  -cutSign t * ((classMult P w t false % 2 : Nat) +
    (classMult P w t true % 2 : Nat) : Int)

private def eventWeight (w : Nat -> Bool) (t : Int) (a b : Bool) (i : Nat) : Int :=
  if layer (wordPos w i) = t then
    if alpha w i = a then if beta w i = b then 1 else 0 else 0 else 0

private theorem eventCount_eq_sum (P : Nat) (w : Nat -> Bool) (t : Int) (a b : Bool) :
    (eventCount P w t a b : Int) =
      ((List.range P).map (eventWeight w t a b)).sum := by
  unfold eventCount
  rw [<- sum_indicator]
  apply sum_congr
  intro i _
  simp only [eventWeight, Bool.and_eq_true, decide_eq_true_eq]
  by_cases ht : layer (wordPos w i) = t <;>
    by_cases ha : alpha w i = a <;> by_cases hb : beta w i = b <;> simp [ht, ha, hb]

/-- Cyclic incidence proves equality of the two actual through-event counts. -/
theorem through_counts_eq {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    eventCount P w t true false = throughCount P w t := by
  have he : ((List.range P).map (fun i =>
      upperWeight w t (prevPhase P i) - upperWeight w t i)).sum = 0 := by
    rw [sum_sub, sum_prev, Int.sub_self]
  have hs : ((List.range P).map (fun i =>
      upperWeight w t (prevPhase P i) - upperWeight w t i)).sum =
      ((List.range P).map (fun i =>
        eventWeight w t true false i - eventWeight w t false true i)).sum := by
    apply sum_congr
    intro i hi
    rw [upper_incidence hh hlv (List.mem_range.mp hi)]
    by_cases ht : layer (wordPos w i) = t <;>
      cases ha : alpha w i <;> cases hb : beta w i <;>
      simp [eventWeight, throughCharge, ht, ha, hb]
  rw [hs, sum_sub, <- eventCount_eq_sum, <- eventCount_eq_sum] at he
  unfold throughCount
  omega

private theorem depCount_sum (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool)
    (d : Direction) :
    (depCount P w t r d : Int) =
      ((classPhases2 P w t r).map (fun i => if outDir w i = d then 1 else 0)).sum := by
  change (((classPhases2 P w t r).filter (fun i => decide (outDir w i = d))).length : Int) = _
  rw [<- sum_indicator]
  apply sum_congr
  intro i _
  simp

private theorem cutFlow_sum (P : Nat) (w : Nat -> Bool) (t : Int) :
    (cutFlow P w t : Int) = ((List.range P).map (fun i =>
      if layer (wordPos w i) = t then if beta w i then (1 : Int) else 0 else 0)).sum := by
  have hl (r : Bool) : (eCnt P w t r : Int) + (nCnt P w t r : Int) =
      ((classPhases2 P w t r).map (fun i => if beta w i then 1 else 0)).sum := by
    rw [depCount_sum, depCount_sum, <- sum_add]
    apply sum_congr
    intro i _
    cases ho : outDir w i <;> simp [beta, ho]
  unfold cutFlow
  simp only [Int.natCast_add]
  rw [show (eCnt P w t false : Int) + nCnt P w t false + eCnt P w t true +
      nCnt P w t true = ((eCnt P w t false : Int) + nCnt P w t false) +
      ((eCnt P w t true : Int) + nCnt P w t true) by omega, hl, hl, two_lane_sum]

theorem cutFlow_eq_bounce_add_through (P : Nat) (w : Nat -> Bool) (t : Int) :
    cutFlow P w t = bounceCount P w t + throughCount P w t := by
  have he : (cutFlow P w t : Int) =
      (eventCount P w t true true : Int) + (eventCount P w t false true : Int) := by
    rw [cutFlow_sum, eventCount_eq_sum, eventCount_eq_sum, <- sum_add]
    apply sum_congr
    intro i _
    by_cases ht : layer (wordPos w i) = t <;>
      cases ha : alpha w i <;> cases hb : beta w i <;>
      simp [eventWeight, ht, ha, hb]
  exact_mod_cast he

private theorem previous_cutFlow {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (t : Int) :
    cutFlow P w (t - 1) = eventCount P w t false false + eventCount P w t true false := by
  rw [cutFlow_eq_cutDownFlow hlv]
  have ht : t - 1 + 1 = t := by omega
  have hl (r : Bool) : (sCnt P w t r : Int) + (wCnt P w t r : Int) =
      ((classPhases2 P w t r).map (fun i => if beta w i then 0 else 1)).sum := by
    rw [depCount_sum, depCount_sum, <- sum_add]
    apply sum_congr
    intro i _
    cases ho : outDir w i <;> simp [beta, ho]
  have he : (cutDownFlow P w (t - 1) : Int) =
      (eventCount P w t false false : Int) + (eventCount P w t true false : Int) := by
    unfold cutDownFlow
    rw [ht]
    simp only [Int.natCast_add]
    rw [show (sCnt P w t false : Int) + wCnt P w t false + sCnt P w t true +
        wCnt P w t true = ((sCnt P w t false : Int) + wCnt P w t false) +
        ((sCnt P w t true : Int) + wCnt P w t true) by omega,
      hl, hl, two_lane_sum, eventCount_eq_sum, eventCount_eq_sum, <- sum_add]
    apply sum_congr
    intro i _
    by_cases ht' : layer (wordPos w i) = t <;>
      cases ha : alpha w i <;> cases hb : beta w i <;>
      simp [eventWeight, ht', ha, hb]
  exact_mod_cast he

private theorem port_color_sign (w : Nat -> Bool) (i : Nat) :
    (if alpha w i = beta w i then (1 : Int) else -1) =
      -cutSign (layer (wordPos w i)) * turnSign (w i) := by
  have hax := inDir_horizontal_eq w i
  cases hd : inDir w i <;> cases hc : w i <;>
    simp [alpha, beta, outDir, hd, hc, turn, Direction.left, Direction.right,
      Direction.horizontal, cutSign, turnSign] at hax ⊢ <;> omega

/-- The paper's A is derived from actual ports and the full stable-rank color history. -/
theorem wakeCharge_eq_event_counts {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    wakeCharge P w t = (eventCount P w t true true : Int) +
      (eventCount P w t false false : Int) -
      (eventCount P w t false true : Int) - (eventCount P w t true false : Int) := by
  have hc (r : Bool) :
      ((classPhases2 P w t r).map (fun i => turnSign (w i))).sum =
        (classMult P w t r % 2 : Nat) := by
    have he := (h.class_turn_counts (classRep t r)).2.2.2
    simpa [hd, classMult, classPhases2, Int.natCast_emod] using he
  have hs := two_lane_sum P w t (fun i => turnSign (w i))
  rw [hc, hc] at hs
  unfold wakeCharge
  rw [hs, <- sum_mul]
  rw [eventCount_eq_sum, eventCount_eq_sum, eventCount_eq_sum, eventCount_eq_sum,
    <- sum_add, <- sum_sub, <- sum_sub]
  apply sum_congr
  intro i _
  by_cases ht : layer (wordPos w i) = t
  · have he := port_color_sign w i
    rw [ht] at he
    cases ha : alpha w i <;> cases hb : beta w i <;>
      simp [eventWeight, ht, ha, hb] at he ⊢ <;> omega
  · simp [eventWeight, ht]

/-- Actual-trajectory local flow equation used in rounds 33--35. -/
theorem local_flow_balance {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    (cutFlow P w (t - 1) : Int) + (cutFlow P w t : Int) =
      wakeCharge P w t + 4 * (throughCount P w t : Int) := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; rfl
  have hu := through_counts_eq h.1 hlv t
  have hf := cutFlow_eq_bounce_add_through P w t
  have hp := previous_cutFlow hlv t
  have ha := wakeCharge_eq_event_counts h hd t
  unfold bounceCount throughCount at *
  omega

/-- Round 34's local defect equation, for actual boundary-event counts.
This statement does not identify the defect with a count of paired runs. -/
theorem event_defect_equation {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    2 * eventDefect P w t = (cutFlow P w t : Int) -
      (cutFlow P w (t - 1) : Int) + wakeCharge P w t := by
  have hf := cutFlow_eq_bounce_add_through P w t
  have hl := local_flow_balance h hd t
  unfold eventDefect
  omega

/-- All visited layers, including the top layer, whose wake charge need not vanish. -/
def layerSum (P : Nat) (w : Nat -> Bool) (f : Int -> Int) : Int :=
  ((List.range ((topLayer P w - botLayer P w).toNat + 1)).map
    (fun k : Nat => f (botLayer P w + (k : Int)))).sum

/-- Round 35's second moment, at an arbitrary integer center. -/
def secondMoment (P : Nat) (w : Nat -> Bool) (c : Int) : Int :=
  2 * layerSum P w (fun t => (t - c) * (t - c) * wakeCharge P w t)

theorem eventDefect_eq_zero_of_cutFlow_eq_zero {P : Nat} {w : Nat -> Bool} {t : Int}
    (hf : cutFlow P w t = 0) : eventDefect P w t = 0 := by
  have he := cutFlow_eq_bounce_add_through P w t
  unfold eventDefect
  omega

theorem eventDefect_eq_zero_at_top {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) : eventDefect P w (topLayer P w) = 0 :=
  eventDefect_eq_zero_of_cutFlow_eq_zero (cutFlow_eq_zero_of_top_le hlv (Int.le_refl _))

theorem upperLength_at_bot {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) :
    upperLength P w (botLayer P w) = (P : Int) := by
  unfold upperLength
  have he : ((List.range P).map (upperWeight w (botLayer P w))).sum =
      ((List.range P).map (fun _ => (1 : Int))).sum := by
    apply sum_congr
    intro i hi
    have hi' := List.mem_range.mp hi
    have h0 := botLayer_le_layer (w := w) hi'
    have h1 := botLayer_le_layer (w := w)
      (nextPhase_lt (P := P) (i := i) (by omega))
    have hc : botLayer P w <= edgeCut w i := by
      rw [edgeCut_eq_min hlv hi']; omega
    simp [upperWeight, hc]
  rw [he]
  have hs (xs : List Nat) : (xs.map (fun _ => (1 : Int))).sum = (xs.length : Int) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  simpa using hs (List.range P)

/-- The total number of upward cut crossings is exactly half the full period. -/
theorem period_eq_twice_cut_sum {P : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) :
    (P : Int) = 2 * sumAbove P w (botLayer P w) (fun t => (cutFlow P w t : Int)) := by
  rw [<- upperLength_eq_twice_sum_cutFlow hlv, upperLength_at_bot hlv]

private theorem sum_range_succ (f : Nat -> Int) (n : Nat) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp [List.range_succ, List.sum_append]

private theorem weighted_difference (a f : Nat -> Int) (n : Nat) :
    ((List.range (n + 1)).map (fun k => a k * (f k - f (k + 1)))).sum =
      a 0 * f 0 - a n * f (n + 1) +
        ((List.range n).map (fun k => (a (k + 1) - a k) * f (k + 1))).sum := by
  induction n with
  | zero => simp [Int.mul_sub]
  | succ n ih =>
    rw [sum_range_succ (fun k => a k * (f k - f (k + 1))) (n + 1), ih,
      sum_range_succ (fun k => (a (k + 1) - a k) * f (k + 1)) n]
    simp only [Int.mul_sub, Int.sub_mul]
    omega

private theorem bot_le_top (P : Nat) (w : Nat -> Bool) : botLayer P w <= topLayer P w := by
  cases P with
  | zero => simp [botLayer, topLayer]
  | succ n =>
    have h0 := botLayer_le_layer (w := w) (i := 0) (P := n + 1) (by omega)
    have h1 := layer_le_topLayer (w := w) (i := 0) (P := n + 1) (by omega)
    omega

private theorem layerSum_eq_sumAbove {P : Nat} {w : Nat -> Bool} {f : Int -> Int}
    (hf : f (topLayer P w) = 0) :
    layerSum P w f = sumAbove P w (botLayer P w) f := by
  have hbt := bot_le_top P w
  have ht : botLayer P w + ((topLayer P w - botLayer P w).toNat : Int) =
      topLayer P w := by omega
  unfold layerSum sumAbove
  rw [sum_range_succ, ht, hf, Int.add_zero]

/-- Finite discrete integration by parts. The bottom and top flux terms are proved zero. -/
theorem weighted_wake_identity {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (a : Int -> Int) :
    layerSum P w (fun t => a t * wakeCharge P w t) =
      2 * sumAbove P w (botLayer P w) (fun t => a t * eventDefect P w t) +
      sumAbove P w (botLayer P w) (fun t =>
        (a (t + 1) - a t) * (cutFlow P w t : Int)) := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; rfl
  have hl : layerSum P w (fun t => a t * wakeCharge P w t) =
      2 * layerSum P w (fun t => a t * eventDefect P w t) +
      layerSum P w (fun t => a t *
        ((cutFlow P w (t - 1) : Int) - (cutFlow P w t : Int))) := by
    unfold layerSum
    rw [<- sum_mul, <- sum_add]
    apply sum_congr
    intro k _
    have he := event_defect_equation h hd (botLayer P w + (k : Int))
    have ha := congrArg (fun z : Int => a (botLayer P w + (k : Int)) * z) he
    simp only [Int.mul_add, Int.mul_sub] at ha
    rw [Int.mul_left_comm _ 2] at ha
    dsimp only
    rw [Int.mul_sub]
    omega
  rw [hl, layerSum_eq_sumAbove (by rw [eventDefect_eq_zero_at_top hlv, Int.mul_zero])]
  congr 1
  let n := (topLayer P w - botLayer P w).toNat
  have ht : botLayer P w + (n : Int) = topLayer P w := by
    have hb := bot_le_top P w
    dsimp [n]
    omega
  have he := weighted_difference (fun k : Nat => a (botLayer P w + (k : Int)))
    (fun k : Nat => (cutFlow P w (botLayer P w + (k : Int) - 1) : Int)) n
  simp only [Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.add_zero,
    show forall k : Int, botLayer P w + (k + 1) - 1 = botLayer P w + k by intro k; omega] at he
  rw [cutFlow_eq_zero_of_lt_bot (by omega), ht,
    cutFlow_eq_zero_of_top_le hlv (Int.le_refl _)] at he
  simpa only [Int.natCast_zero, Int.mul_zero, Int.sub_self, Int.zero_add,
    layerSum, sumAbove, n, Int.add_assoc] using he

private theorem square_step (z : Int) : (z + 1) * (z + 1) - z * z = 2 * z + 1 := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  omega

/-- Round 35, equation (35.1), with the actual boundary-event defect B-u.
The identification B-u=BB-TT requires the separate excursion endpoint bijection.
No excursion length assumption enters this identity. -/
theorem secondMoment_event_defect_expansion {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (c : Int) :
    secondMoment P w c = (P : Int) +
      4 * sumAbove P w (botLayer P w) (fun t =>
        (t - c) * (cutFlow P w t : Int) + (t - c) * (t - c) * eventDefect P w t) := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; rfl
  have he := weighted_wake_identity h hd (fun t => (t - c) * (t - c))
  have hs : sumAbove P w (botLayer P w) (fun t =>
      (((t + 1) - c) * ((t + 1) - c) - (t - c) * (t - c)) * (cutFlow P w t : Int)) =
      2 * sumAbove P w (botLayer P w) (fun t => (t - c) * (cutFlow P w t : Int)) +
      sumAbove P w (botLayer P w) (fun t => (cutFlow P w t : Int)) := by
    unfold sumAbove
    rw [<- sum_mul, <- sum_add]
    apply sum_congr
    intro k _
    dsimp only
    rw [show botLayer P w + (k : Int) + 1 - c = (botLayer P w + (k : Int) - c) + 1 by omega,
      square_step, Int.add_mul, Int.one_mul, Int.mul_assoc]
  rw [hs] at he
  have hp := period_eq_twice_cut_sum hlv
  unfold secondMoment
  rw [he]
  unfold sumAbove at hp ⊢
  rw [sum_add]
  dsimp only at hp ⊢
  omega

/-- Cyclic phase at offset k, without forgetting a full-period endpoint. -/
def phase (P i k : Nat) : Nat := (i + k) % P

private theorem phase_zero {P i : Nat} (hi : i < P) : phase P i 0 = i := by
  simp [phase, Nat.mod_eq_of_lt hi]

private theorem phase_period {P i : Nat} (hi : i < P) : phase P i P = i := by
  simp [phase, Nat.mod_eq_of_lt hi]

private theorem phase_succ (P i k : Nat) : phase P i (k + 1) = nextPhase P (phase P i k) := by
  simp only [phase, nextPhase, Nat.mod_add_mod, Nat.add_assoc]

private theorem phase_add (P i k n : Nat) : phase P (phase P i k) n = phase P i (k + n) := by
  simp only [phase, Nat.mod_add_mod, Nat.add_assoc]

private theorem phase_small {P i k : Nat} (hi : i < P) (hk : k <= P) :
    phase P i k = if i + k < P then i + k else i + k - P := by
  unfold phase
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem phase_injective_offset {P i a b : Nat}
    (hi : i < P) (ha : a < P) (hb : b < P)
    (he : phase P i a = phase P i b) : a = b := by
  rw [phase_small hi (by omega), phase_small hi (by omega)] at he
  split at he <;> split at he <;> omega

/-- An upper excursion: its interior is strictly above t, so a bounce splits
two excursions. The endpoint length bound is non-strict, as in round 40. -/
structure UpperRun (P : Nat) (w : Nat -> Bool) (t : Int) (i len : Nat) : Prop where
  start_lt : i < P
  length_pos : 0 < len
  length_le : len <= P
  start_layer : layer (wordPos w i) = t
  end_layer : layer (wordPos w (phase P i len)) = t
  inside : forall k, 0 < k -> k < len -> t < layer (wordPos w (phase P i k))
  upward : beta w i = true

/-- First weak return to the boundary, searched over offsets 1,...,P. -/
def runLength (P : Nat) (w : Nat -> Bool) (t : Int) (i : Nat) : Nat :=
  (List.range P).findIdx (fun k => decide (layer (wordPos w (phase P i (k + 1))) <= t)) + 1

def runEnd (P : Nat) (w : Nat -> Bool) (t : Int) (i : Nat) : Nat :=
  phase P i (runLength P w t i)

def runStarts (P : Nat) (w : Nat -> Bool) (t : Int) : List Nat :=
  (List.range P).filter (fun i => decide (layer (wordPos w i) = t) && beta w i)

def runEnds (P : Nat) (w : Nat -> Bool) (t : Int) : List Nat :=
  (List.range P).filter (fun i => decide (layer (wordPos w i) = t) && alpha w i)

private theorem mem_runStarts {P i : Nat} {w : Nat -> Bool} {t : Int} :
    i ∈ runStarts P w t <-> i < P /\ layer (wordPos w i) = t /\ beta w i = true := by
  simp [runStarts]

private theorem mem_runEnds {P i : Nat} {w : Nat -> Bool} {t : Int} :
    i ∈ runEnds P w t <-> i < P /\ layer (wordPos w i) = t /\ alpha w i = true := by
  simp [runEnds]

private theorem phase_layer_step {P i : Nat} {w : Nat -> Bool}
    (hlv : layer (wordDrift P w) = 0) (hi : i < P) (k : Nat) :
    layer (wordPos w (phase P i (k + 1))) = layer (wordPos w (phase P i k)) +
      layerDelta (outDir w (phase P i k)) := by
  rw [phase_succ]
  exact layer_wordPos_nextPhase_of_layer_zero hlv (Nat.mod_lt _ (by omega))

/-- Every actual upward boundary departure produces an upper run, including L=P. -/
theorem runLength_spec {P i : Nat} {w : Nat -> Bool} {t : Int}
    (hlv : layer (wordDrift P w) = 0) (hi : i ∈ runStarts P w t) :
    UpperRun P w t i (runLength P w t i) := by
  obtain ⟨hiP, hit, hib⟩ := mem_runStarts.mp hi
  let test := fun k => decide (layer (wordPos w (phase P i (k + 1))) <= t)
  have hex : exists k, k ∈ List.range P /\ test k = true := by
    refine ⟨P - 1, List.mem_range.mpr (by omega), ?_⟩
    dsimp [test]
    rw [show P - 1 + 1 = P by omega, phase_period hiP, hit]
    simp
  have hlt := List.findIdx_lt_length_of_exists hex
  have htst := List.findIdx_getElem (w := hlt)
  simp only [List.length_range] at hlt
  simp only [List.getElem_range] at htst
  have hend : layer (wordPos w (phase P i (runLength P w t i))) <= t := by
    exact of_decide_eq_true htst
  have hin (k : Nat) (hk0 : 0 < k) (hk : k < runLength P w t i) :
      t < layer (wordPos w (phase P i k)) := by
    have hf := List.not_of_lt_findIdx (xs := List.range P) (p := test)
      (i := k - 1) (show k - 1 < (List.range P).findIdx test by
        change k < (List.range P).findIdx test + 1 at hk
        omega)
    simp only [List.getElem_range, test, show k - 1 + 1 = k by omega,
      decide_eq_false_iff_not] at hf
    omega
  have hpos : 0 < runLength P w t i := by unfold runLength; omega
  have hle : runLength P w t i <= P := by exact Nat.succ_le_of_lt hlt
  have htwo : 2 <= runLength P w t i := by
    by_cases hn : 2 <= runLength P w t i
    · exact hn
    · have he : runLength P w t i = 1 := by omega
      have hs := phase_layer_step hlv hiP 0
      rw [phase_zero hiP, hit] at hs
      rw [he] at hend
      cases ho : outDir w i <;> simp [beta, ho, layerDelta] at hib hs <;> omega
  have hprev := hin (runLength P w t i - 1) (by omega) (by omega)
  have hs := phase_layer_step hlv hiP (runLength P w t i - 1)
  rw [show runLength P w t i - 1 + 1 = runLength P w t i by omega] at hs
  have heq : layer (wordPos w (phase P i (runLength P w t i))) = t := by
    cases ho : outDir w (phase P i (runLength P w t i - 1)) <;>
      simp [ho, layerDelta] at hs <;> omega
  exact ⟨hiP, hpos, hle, hit, heq, hin, hib⟩

theorem UpperRun.length_ge_two {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (hlv : layer (wordDrift P w) = 0) : 2 <= len := by
  have hs := phase_layer_step hlv r.start_lt 0
  rw [phase_zero r.start_lt, r.start_layer] at hs
  have hb := r.upward
  have he := r.end_layer
  by_cases hn : 2 <= len
  · exact hn
  · have hl : len = 1 := by have := r.length_pos; omega
    rw [hl] at he
    cases ho : outDir w i <;> simp [beta, ho, layerDelta] at hb hs <;> omega

theorem UpperRun.end_alpha {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (hh : (wordTrace w P).2 = .north)
    (hlv : layer (wordDrift P w) = 0) : alpha w (phase P i len) = true := by
  have hl := r.length_ge_two hlv
  have hp := r.inside (len - 1) (by omega) (by omega)
  have hs := phase_layer_step hlv r.start_lt (len - 1)
  rw [show len - 1 + 1 = len by omega, r.end_layer] at hs
  have hn : nextPhase P (phase P i (len - 1)) = phase P i len := by
    rw [<- phase_succ, show len - 1 + 1 = len by omega]
  have hd := outDir_prevPhase hh (show phase P i len < P from Nat.mod_lt _ (by have := r.start_lt; omega))
  have hprev : prevPhase P (phase P i len) = phase P i (len - 1) := by
    rw [<- hn]
    exact prevPhase_nextPhase (show phase P i (len - 1) < P from
      Nat.mod_lt _ (by have := r.start_lt; omega))
  rw [hprev] at hd
  unfold alpha
  rw [<- hd]
  cases ho : outDir w (phase P i (len - 1)) <;> simp [ho, layerDelta] at hs ⊢ <;> omega

/-- Equality of two valid runs with a common start; their lengths cannot be chosen freely. -/
theorem UpperRun.length_unique {P i a b : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i a) (s : UpperRun P w t i b) : a = b := by
  by_cases hab : a < b
  · have := s.inside a r.length_pos hab
    rw [r.end_layer] at this
    omega
  · by_cases hba : b < a
    · have := r.inside b s.length_pos hba
      rw [s.end_layer] at this
      omega
    · omega

/-- A full-period run has the same endpoint phase; this case is intentionally allowed. -/
theorem UpperRun.full_period_end {P i : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i P) : phase P i P = i := phase_period r.start_lt

private theorem phase_cancel_end {P i j a b : Nat}
    (hi : i < P) (hj : j < P) (ha : a <= P) (hb : b <= P) (hab : a <= b)
    (he : phase P i a = phase P j b) : phase P j (b - a) = i := by
  rw [phase_small hi ha, phase_small hj hb] at he
  rw [phase_small hj (show b - a <= P by omega)]
  split at he <;> split at he <;> split <;> omega

/-- Distinct upward departures cannot share a terminal occurrence. -/
theorem UpperRun.end_injective {P i j a b : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i a) (s : UpperRun P w t j b)
    (he : phase P i a = phase P j b) : i = j := by
  by_cases hab : a < b
  · have hf := phase_cancel_end r.start_lt s.start_lt r.length_le s.length_le
      (Nat.le_of_lt hab) he
    have hs := s.inside (b - a) (by omega) (by have := r.length_pos; omega)
    rw [hf, r.start_layer] at hs
    omega
  · have hf := phase_cancel_end s.start_lt r.start_lt s.length_le r.length_le
      (by omega) he.symm
    by_cases hba : b < a
    · have hr := r.inside (a - b) (by omega) (by have := s.length_pos; omega)
      rw [hf, s.start_layer] at hr
      omega
    · have heq : a = b := by omega
      rw [heq, Nat.sub_self, phase_zero r.start_lt] at hf
      exact hf

theorem runStarts_length (P : Nat) (w : Nat -> Bool) (t : Int) :
    (runStarts P w t).length = cutFlow P w t := by
  have he := cutFlow_sum P w t
  unfold runStarts
  have hs := sum_indicator (List.range P)
    (fun i => decide (layer (wordPos w i) = t) && beta w i)
  have he' : ((List.range P).map (fun i =>
      if layer (wordPos w i) = t then if beta w i then (1 : Int) else 0 else 0)).sum =
      ((List.range P).map (fun i =>
        if decide (layer (wordPos w i) = t) && beta w i then (1 : Int) else 0)).sum := by
    apply sum_congr
    intro i _
    by_cases ht : layer (wordPos w i) = t <;> simp [ht]
  rw [he'] at he
  omega

private theorem runEnds_length {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    (runEnds P w t).length = (runStarts P w t).length := by
  have he : ((runEnds P w t).length : Int) =
      (bounceCount P w t : Int) + (eventCount P w t true false : Int) := by
    unfold runEnds
    rw [<- sum_indicator, eventCount_eq_sum, eventCount_eq_sum, <- sum_add]
    apply sum_congr
    intro i _
    by_cases ht : layer (wordPos w i) = t <;>
      cases ha : alpha w i <;> cases hb : beta w i <;> simp [eventWeight, ht, ha, hb]
  rw [through_counts_eq hh hlv] at he
  have hf := cutFlow_eq_bounce_add_through P w t
  rw [runStarts_length]
  omega

private theorem nodup_map_on {A B : Type} {xs : List A} (f : A -> B) (hn : xs.Nodup)
    (hf : forall i, i ∈ xs -> forall j, j ∈ xs -> f i = f j -> i = j) :
    (xs.map f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  have hi' : i < xs.length := by simpa using hi
  have hj' : j < xs.length := by simpa using hj
  simp only [List.getElem_map] at he
  exact (List.nodup_iff_eq_of_getElem_eq.mp hn) i j hi' hj'
    (hf _ (List.getElem_mem hi') _ (List.getElem_mem hj') he)

private theorem perm_of_nodup_subset_length {A : Type} [DecidableEq A]
    {xs ys : List A} (hx : xs.Nodup) (hy : ys.Nodup)
    (hs : xs ⊆ ys) (hl : xs.length = ys.length) : xs.Perm ys := by
  apply (List.perm_ext_iff_of_nodup hx hy).mpr
  intro a
  constructor
  · intro ha; exact hs ha
  · intro ha
    by_cases ham : a ∈ xs
    · exact ham
    · have hn : (a :: xs).Nodup := List.nodup_cons.mpr ⟨ham, hx⟩
      have hsub : a :: xs ⊆ ys := by
        intro b hb
        rcases List.mem_cons.mp hb with he | hb
        · simpa [he] using ha
        · exact hs hb
      have hlen := hn.length_le_of_subset hsub
      simp only [List.length_cons] at hlen
      omega

/-- The terminal phases are a permutation of all actual downward arrivals.
This is the endpoint-occurrence bijection, with seam and full-period cases. -/
theorem runEnd_perm {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    ((runStarts P w t).map (runEnd P w t)).Perm (runEnds P w t) := by
  apply perm_of_nodup_subset_length
  · apply nodup_map_on _ (List.nodup_range.filter _)
    intro i hi j hj he
    exact (runLength_spec hlv hi).end_injective (runLength_spec hlv hj) he
  · exact List.nodup_range.filter _
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have hr := runLength_spec hlv hi
    exact mem_runEnds.mpr ⟨Nat.mod_lt _ (by have := hr.start_lt; omega),
      hr.end_layer, hr.end_alpha hh hlv⟩
  · rw [List.length_map, runEnds_length hh hlv]

/-- True denotes B and false T at each endpoint of a real upper run.
At the start beta=true, so its type is alpha; at the end alpha=true,
so its type is beta. These are endpoint types, not the board colors. -/
def runCount (P : Nat) (w : Nat -> Bool) (t : Int) (a b : Bool) : Nat :=
  ((runStarts P w t).filter (fun i => decide (alpha w i = a) &&
    decide (beta w (runEnd P w t i) = b))).length

abbrev BB (P : Nat) (w : Nat -> Bool) (t : Int) := runCount P w t true true
abbrev BT (P : Nat) (w : Nat -> Bool) (t : Int) := runCount P w t true false
abbrev TB (P : Nat) (w : Nat -> Bool) (t : Int) := runCount P w t false true
abbrev TT (P : Nat) (w : Nat -> Bool) (t : Int) := runCount P w t false false

/-- The run defect q is the actual difference BB-TT. -/
def runDefect (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  (BB P w t : Int) - (TT P w t : Int)

private theorem split_filter (xs : List Nat) (p q : Nat -> Bool) :
    (xs.filter (fun i => p i && q i)).length +
      (xs.filter (fun i => p i && !(q i))).length = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases hp : p i <;> cases hq : q i <;> simp [hp, hq] <;> omega

private theorem runCount_start (P : Nat) (w : Nat -> Bool) (t : Int) (a : Bool) :
    runCount P w t a true + runCount P w t a false = eventCount P w t a true := by
  unfold runCount
  simp only [Bool.decide_coe, Bool.decide_eq_false]
  rw [split_filter]
  unfold runStarts eventCount
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro i _
  cases alpha w i <;> cases beta w i <;> cases a <;>
    by_cases ht : layer (wordPos w i) = t <;> simp [ht]

private theorem runCount_end {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) (b : Bool) :
    runCount P w t true b + runCount P w t false b = eventCount P w t true b := by
  have hs := split_filter (runStarts P w t)
    (fun i => decide (beta w (runEnd P w t i) = b)) (alpha w)
  have he := ((runEnd_perm hh hlv t).filter (fun i => decide (beta w i = b))).length_eq
  rw [List.filter_map, List.length_map] at he
  have hr : ((runEnds P w t).filter (fun i => decide (beta w i = b))).length =
      eventCount P w t true b := by
    unfold runEnds eventCount
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro i _
    by_cases ht : layer (wordPos w i) = t <;>
      cases alpha w i <;> cases beta w i <;> cases b <;> simp [ht]
  rw [hr] at he
  unfold runCount
  dsimp only [Function.comp_def] at he
  rw [he] at hs
  simpa only [Bool.decide_coe, Bool.decide_eq_false, Bool.and_comm] using hs

/-- Round 34: all four endpoint-incidence counts are derived from real runs. -/
theorem endpoint_incidence {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    BB P w t + BT P w t = bounceCount P w t /\
    BB P w t + TB P w t = bounceCount P w t /\
    TB P w t + TT P w t = throughCount P w t /\
    BT P w t + TT P w t = throughCount P w t := by
  exact ⟨runCount_start P w t true, runCount_end hh hlv t true,
    runCount_start P w t false,
    (runCount_end hh hlv t false).trans (through_counts_eq hh hlv t)⟩

/-- Round 34's endpoint-association equations, with B counted at both ends. -/
theorem endpoint_incidence_totals {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    2 * bounceCount P w t = 2 * BB P w t + BT P w t + TB P w t /\
    2 * throughCount P w t = 2 * TT P w t + BT P w t + TB P w t /\
    cutFlow P w t = BB P w t + BT P w t + TB P w t + TT P w t := by
  obtain ⟨hb0, hb1, ht0, ht1⟩ := endpoint_incidence hh hlv t
  have hf := cutFlow_eq_bounce_add_through P w t
  omega

/-- Round 34: the actual paired-run defect equals B-u=f-2u. -/
theorem runDefect_eq_eventDefect {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0) (t : Int) :
    runDefect P w t = eventDefect P w t := by
  obtain ⟨hb, _, _, ht⟩ := endpoint_incidence hh hlv t
  unfold runDefect eventDefect
  omega

/-- Round 34, equation (34.1), now for the actual BB/BT/TB/TT run classification. -/
theorem same_colour_endpoint_defect {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    2 * ((BB P w t : Int) - (TT P w t : Int)) =
      (cutFlow P w t : Int) - (cutFlow P w (t - 1) : Int) + wakeCharge P w t := by
  change 2 * runDefect P w t = _
  rw [runDefect_eq_eventDefect h.1 (by rw [hd]; rfl)]
  exact event_defect_equation h hd t

/-- Round 35, equation (35.1), with q=BB-TT over actual runs. -/
theorem secondMoment_defect_expansion {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (c : Int) :
    secondMoment P w c = (P : Int) +
      4 * sumAbove P w (botLayer P w) (fun t =>
        (t - c) * (cutFlow P w t : Int) + (t - c) * (t - c) * runDefect P w t) := by
  have he : runDefect P w = eventDefect P w := by
    funext t
    exact runDefect_eq_eventDefect h.1 (by rw [hd]; rfl) t
  rw [he]
  exact secondMoment_event_defect_expansion h hd c

/-- The physical lifted path of a run, including any period seam. -/
def runPath {P : Nat} (hP : 0 < P) (w : Nat -> Bool) (t : Int) (i : Nat) :
    ContinuousPhasePath P (runLength P w t i) :=
  ContinuousPhasePath.ofStart hP i (runLength P w t i)

private theorem path_layer {P len : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) (hlv : layer (wordDrift P w) = 0) (k : Nat) :
    layer (p.pos w k) = layer (wordPos w (p.phase k)) := by
  simp [ContinuousPhasePath.pos, biPeriodicPos, layer_addPoint, layer_scalePoint, hlv]

/-- Actual equal endpoint colors for BB and TT, independent of consistency. -/
theorem UpperRun.same_colour {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (hh : (wordTrace w P).2 = .north)
    (hlv : layer (wordDrift P w) = 0)
    (htype : alpha w i = beta w (phase P i len)) : w i = w (phase P i len) := by
  have h0 := port_color_sign w i
  have h1 := port_color_sign w (phase P i len)
  rw [r.start_layer, r.upward] at h0
  rw [r.end_layer, r.end_alpha hh hlv, <- htype] at h1
  cases ha : alpha w i <;> cases hc0 : w i <;> cases hc1 : w (phase P i len) <;>
    by_cases ht : t % 2 = 0 <;> simp [ha, hc0, hc1, turnSign, cutSign, ht] at h0 h1 ⊢

/-- A physical first return flips the color. Applied to an upper run, strict
interiority discharges the no-intermediate-return condition. -/
theorem UpperRun.return_colour_ne {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (h : ConsistentWord P w)
    (hd : wordDrift P w = (2, -2))
    (hret : (ContinuousPhasePath.ofStart h.pos_period i len).pos w len =
      (ContinuousPhasePath.ofStart h.pos_period i len).pos w 0) :
    w i ≠ w (phase P i len) := by
  let p := ContinuousPhasePath.ofStart h.pos_period i len
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; rfl
  have hstart : p.phase 0 = i := phase_zero r.start_lt
  have hr := Drift.path_firstReturn_rank p hd drift_two_negTwo_ne_zero r.length_pos hret
    (fun k hk0 hkl he => by
      have hh := congrArg layer he
      rw [path_layer p hlv, path_layer p hlv, hstart, r.start_layer] at hh
      have hi := r.inside k hk0 hkl
      change t < layer (wordPos w (p.phase k)) at hi
      omega)
  rw [hstart] at hr
  intro he
  change w i = w (p.phase len) at he
  rw [Drift.consistentWord_stableRank_color h r.start_lt,
    Drift.consistentWord_stableRank_color h (p.phase_lt len (Nat.le_refl _))] at he
  have hb := Bool.eq_iff_iff.mp he
  simp only [decide_eq_true_eq, hr] at hb
  omega

/-- Same-type runs are non-returning in physical space, even when their phases agree. -/
theorem UpperRun.same_type_nonreturn {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (h : ConsistentWord P w)
    (hd : wordDrift P w = (2, -2))
    (htype : alpha w i = beta w (phase P i len)) :
    (ContinuousPhasePath.ofStart h.pos_period i len).pos w len ≠
      (ContinuousPhasePath.ofStart h.pos_period i len).pos w 0 := by
  intro he
  exact r.return_colour_ne h hd he (r.same_colour h.1 (by rw [hd]; rfl) htype)

/-- Computable physical endpoint, with the quotient carry retained. -/
def runEndPos (P : Nat) (w : Nat -> Bool) (t : Int) (i : Nat) : Point :=
  biPeriodicPos P w (((i + runLength P w t i) / P : Nat) : Int) (runEnd P w t i)

def nonreturnCount (P : Nat) (w : Nat -> Bool) (t : Int) : Nat :=
  ((runStarts P w t).filter (fun i => decide (runEndPos P w t i ≠ wordPos w i))).length

private theorem ofStart_pos_zero {P i len : Nat} {w : Nat -> Bool} (hi : i < P) (hP : 0 < P) :
    (ContinuousPhasePath.ofStart hP i len).pos w 0 = wordPos w i := by
  simp only [ContinuousPhasePath.pos, ContinuousPhasePath.ofStart, biPeriodicPos,
    Nat.add_zero, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, Int.natCast_zero,
    scalePoint, addPoint, Int.zero_mul, Int.add_zero]

private theorem same_type_nonreturn_at_start {P i : Nat} {w : Nat -> Bool} {t : Int}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i ∈ runStarts P w t) (htype : alpha w i = beta w (runEnd P w t i)) :
    runEndPos P w t i ≠ wordPos w i := by
  have r := runLength_spec (show layer (wordDrift P w) = 0 by rw [hd]; rfl) hi
  have he := r.same_type_nonreturn h hd htype
  rw [ofStart_pos_zero r.start_lt] at he
  exact he

/-- Round 34: every BB or TT occurrence contributes to N; mixed nonreturns remain allowed. -/
theorem same_type_le_nonreturn {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    BB P w t + TT P w t <= nonreturnCount P w t := by
  let xs := (runStarts P w t).filter (fun i => decide (alpha w i = beta w (runEnd P w t i)))
  have hn : xs.Nodup := (List.nodup_range.filter _).filter _
  have hs : xs ⊆ (runStarts P w t).filter (fun i => decide (runEndPos P w t i ≠ wordPos w i)) := by
    intro i hi
    obtain ⟨hi, he⟩ := List.mem_filter.mp hi
    exact List.mem_filter.mpr ⟨hi, by simpa using same_type_nonreturn_at_start h hd hi (of_decide_eq_true he)⟩
  have hl := hn.length_le_of_subset hs
  have he : BB P w t + TT P w t = xs.length := by
    unfold BB TT runCount xs
    generalize runStarts P w t = ls
    induction ls with
    | nil => rfl
    | cons i ls ih =>
      simp only [Bool.decide_coe, Bool.decide_eq_false] at ih
      cases ha : alpha w i <;> cases hb : beta w (runEnd P w t i) <;>
        simp [ha, hb] <;> omega
  rw [he]
  exact hl

/-- Round 33, equation (33.1), as a two-sided integer bound (equivalently an absolute value). -/
theorem nonreturn_discrete_derivative_bound {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    -(2 * (nonreturnCount P w t : Int)) <=
        (cutFlow P w t : Int) - (cutFlow P w (t - 1) : Int) + wakeCharge P w t /\
    (cutFlow P w t : Int) - (cutFlow P w (t - 1) : Int) + wakeCharge P w t <=
      2 * (nonreturnCount P w t : Int) := by
  have hn := same_type_le_nonreturn h hd t
  have he := same_colour_endpoint_defect h hd t
  omega

/-- Physical returns, using lifted endpoints rather than phase equality. -/
def returnCount (P : Nat) (w : Nat -> Bool) (t : Int) : Nat :=
  ((runStarts P w t).filter (fun i => decide (runEndPos P w t i = wordPos w i))).length

theorem nonreturn_add_return (P : Nat) (w : Nat -> Bool) (t : Int) :
    nonreturnCount P w t + returnCount P w t = cutFlow P w t := by
  rw [<- runStarts_length]
  unfold nonreturnCount returnCount
  generalize runStarts P w t = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [ne_eq, decide_not] at ih
    by_cases he : runEndPos P w t i = wordPos w i <;> simp [he] <;> omega

/-- Round 33: both return-incidence bounds are consequences of actual run counts. -/
theorem return_incidence_bounds {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) :
    returnCount P w t <= 2 * bounceCount P w t /\
      returnCount P w t <= 2 * throughCount P w t := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; rfl
  obtain ⟨hb0, hb1, ht0, ht1⟩ := endpoint_incidence h.1 hlv t
  have hn := same_type_le_nonreturn h hd t
  have hs := nonreturn_add_return P w t
  have hf := cutFlow_eq_bounce_add_through P w t
  omega

private theorem phase_reaches {P i j : Nat} (hi : i < P) (hj : j < P) :
    exists k, 0 < k /\ k <= P /\ phase P i k = j := by
  by_cases hij : i < j
  · refine ⟨j - i, by omega, by omega, ?_⟩
    rw [phase_small hi (by omega), ite_eq_left (by omega)]
    omega
  · refine ⟨P + j - i, by omega, by omega, ?_⟩
    rw [phase_small hi (by omega), ite_eq_right (by omega)]
    omega

/-- Every selected edge reaches the boundary before one full period, provided
the cut is not below the entire path. This condition is necessary for coverage. -/
private theorem edge_tail {P i : Nat} {w : Nat -> Bool} {t : Int}
    (hlv : layer (wordDrift P w) = 0) (hi : i < P)
    (hbot : botLayer P w <= t) (hupper : t <= edgeCut w i) :
    exists n, 0 < n /\ n <= P /\ layer (wordPos w (phase P i n)) = t /\
      (forall k, 0 < k -> k < n -> t < layer (wordPos w (phase P i k))) := by
  obtain ⟨j, hj, hjbot⟩ := exists_botLayer_phase (w := w) (show 0 < P by omega)
  obtain ⟨k, hk0, hkP, hkj⟩ := phase_reaches hi hj
  let test := fun k => decide (layer (wordPos w (phase P i (k + 1))) <= t)
  have hex : exists k, k ∈ List.range P /\ test k = true := by
    refine ⟨k - 1, List.mem_range.mpr (by omega), ?_⟩
    dsimp [test]
    rw [show k - 1 + 1 = k by omega, hkj, hjbot]
    exact decide_eq_true hbot
  have hlt := List.findIdx_lt_length_of_exists hex
  have htst := List.findIdx_getElem (w := hlt)
  simp only [List.length_range] at hlt
  simp only [List.getElem_range] at htst
  let n := (List.range P).findIdx test + 1
  have hn0 : 0 < n := by dsimp [n]; omega
  have hnP : n <= P := by dsimp [n]; omega
  have hn : layer (wordPos w (phase P i n)) <= t := of_decide_eq_true htst
  have hin (r : Nat) (hr0 : 0 < r) (hr : r < n) : t < layer (wordPos w (phase P i r)) := by
    have hf := List.not_of_lt_findIdx (xs := List.range P) (p := test)
      (i := r - 1) (show r - 1 < (List.range P).findIdx test by dsimp [n] at hr; omega)
    simp only [List.getElem_range, test, show r - 1 + 1 = r by omega,
      decide_eq_false_iff_not] at hf
    omega
  refine ⟨n, hn0, hnP, ?_, hin⟩
  by_cases hn1 : n = 1
  · rw [edgeCut_eq_min hlv hi] at hupper
    have he : phase P i n = nextPhase P i := by
      rw [hn1, show (1 : Nat) = 0 + 1 by rfl, phase_succ, phase_zero hi]
    rw [he] at hn ⊢
    omega
  · have hp := hin (n - 1) (by omega) (by omega)
    have hs := phase_layer_step hlv hi (n - 1)
    rw [show n - 1 + 1 = n by omega] at hs
    cases ho : outDir w (phase P i (n - 1)) <;> simp [ho, layerDelta] at hs <;> omega

theorem UpperRun.edge_upper {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (hlv : layer (wordDrift P w) = 0)
    {k : Nat} (hk : k < len) : t <= edgeCut w (phase P i k) := by
  have hp : forall k, k <= len -> t <= layer (wordPos w (phase P i k)) := by
    intro k hk
    by_cases h0 : k = 0
    · simp [h0, phase_zero r.start_lt, r.start_layer]
    · by_cases he : k = len
      · rw [he, r.end_layer]
        exact Int.le_refl _
      · have := r.inside k (by omega) (by omega); omega
  have h0 := hp k (by omega)
  have h1 := hp (k + 1) (by omega)
  rw [phase_succ] at h1
  rw [edgeCut_eq_min hlv (show phase P i k < P from
    Nat.mod_lt _ (by have := r.start_lt; omega))]
  omega

/-- Every upper-edge occurrence belongs to an actual upper run. -/
theorem edge_has_run {P i : Nat} {w : Nat -> Bool} {t : Int}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hbot : botLayer P w <= t) (hi : i < P) (hupper : t <= edgeCut w i) :
    exists j, j ∈ runStarts P w t /\
      exists k, k < runLength P w t j /\ phase P j k = i := by
  obtain ⟨n, hn0, hnP, hnt, hin⟩ := edge_tail hlv hi hbot hupper
  have hprev : t < layer (wordPos w (phase P i (n - 1))) := by
    by_cases hn1 : n = 1
    · have hs := phase_layer_step hlv hi 0
      rw [phase_zero hi, show 0 + 1 = n by omega, hnt] at hs
      rw [edgeCut_eq_min hlv hi] at hupper
      have hcur : t <= layer (wordPos w i) := by omega
      rw [hn1, Nat.sub_self, phase_zero hi]
      cases ho : outDir w i <;> simp [ho, layerDelta] at hs <;> omega
    · exact hin (n - 1) (by omega) (by omega)
  have hph : phase P i n < P := Nat.mod_lt _ (by omega)
  have hp : prevPhase P (phase P i n) = phase P i (n - 1) := by
    have hs : phase P i n = nextPhase P (phase P i (n - 1)) := by
      rw [<- phase_succ, show n - 1 + 1 = n by omega]
    rw [hs]
    exact prevPhase_nextPhase (show phase P i (n - 1) < P from Nat.mod_lt _ (by omega))
  have hs := layer_wordPos_prevPhase_of_layer_zero hh hlv hph
  rw [hp, hnt] at hs
  have ha : alpha w (phase P i n) = true := by
    cases hd : inDir w (phase P i n) <;> simp [alpha, hd, layerDelta] at hs ⊢ <;> omega
  have hem := (runEnd_perm hh hlv t).mem_iff.mpr (mem_runEnds.mpr ⟨hph, hnt, ha⟩)
  obtain ⟨j, hj, hje⟩ := List.mem_map.mp hem
  have r := runLength_spec hlv hj
  have hnle : n <= runLength P w t j := by
    by_cases hle : n <= runLength P w t j
    · exact hle
    · have he := phase_cancel_end r.start_lt hi r.length_le hnP (by omega) hje
      have hg := hin (n - runLength P w t j) (by omega) (by have := r.length_pos; omega)
      rw [he, r.start_layer] at hg
      omega
  refine ⟨j, hj, runLength P w t j - n, by omega, ?_⟩
  exact phase_cancel_end hi r.start_lt hnP r.length_le hnle hje.symm

/-- A selected edge cannot belong to two runs or to two offsets in one run. -/
theorem run_edge_unique {P i j a b k l : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i a) (s : UpperRun P w t j b)
    (hk : k < a) (hl : l < b) (he : phase P i k = phase P j l) : i = j /\ k = l := by
  have hkP : k < P := by have := r.length_le; omega
  have hlP : l < P := by have := s.length_le; omega
  have hkl : k = l := by
    by_cases hkl : k < l
    · have hc := phase_cancel_end r.start_lt s.start_lt (by omega) (by omega) (by omega) he
      have hs := s.inside (l - k) (by omega) (by omega)
      rw [hc, r.start_layer] at hs
      omega
    · by_cases hlk : l < k
      · have hc := phase_cancel_end s.start_lt r.start_lt (by omega) (by omega) (by omega) he.symm
        have hr := r.inside (k - l) (by omega) (by omega)
        rw [hc, s.start_layer] at hr
        omega
      · omega
  have hc := phase_cancel_end r.start_lt s.start_lt (by omega) (by omega) (by omega) he
  rw [hkl, Nat.sub_self, phase_zero s.start_lt] at hc
  exact ⟨hc.symm, hkl⟩

/-- An edge occurrence is tagged by its departure run and its offset in that run. -/
def runEdgeOccurrences (P : Nat) (w : Nat -> Bool) (t : Int) : List (Nat × Nat) :=
  (runStarts P w t).flatMap (fun i =>
    (List.range (runLength P w t i)).map (fun k => (i, k)))

private theorem mem_runEdgeOccurrences {P i k : Nat} {w : Nat -> Bool} {t : Int} :
    (i, k) ∈ runEdgeOccurrences P w t <-> i ∈ runStarts P w t /\ k < runLength P w t i := by
  simp [runEdgeOccurrences]

private theorem runEdgeOccurrences_nodup (P : Nat) (w : Nat -> Bool) (t : Int) :
    (runEdgeOccurrences P w t).Nodup := by
  unfold runEdgeOccurrences
  change List.Pairwise _ _
  rw [List.pairwise_flatMap]
  constructor
  · intro i _
    exact nodup_map_on _ List.nodup_range (fun a _ b _ he => congrArg Prod.snd he)
  · have hn : (runStarts P w t).Nodup := List.nodup_range.filter _
    apply List.Pairwise.imp _ hn
    intro i j hij x hx y hy he
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hy
    exact hij (congrArg Prod.fst he)

/-- The complete edge-occurrence bijection. A cut below botLayer has no run
starts but still has P upper edges, so that case is correctly excluded here. -/
theorem runEdgeOccurrence_perm {P : Nat} {w : Nat -> Bool} {t : Int}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hbot : botLayer P w <= t) :
    ((runEdgeOccurrences P w t).map (fun p => phase P p.1 p.2)).Perm
      ((List.range P).filter (fun i => decide (t <= edgeCut w i))) := by
  apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range.filter _)).mpr
  · intro i
    constructor
    · intro hi
      obtain ⟨⟨j, k⟩, hjk, rfl⟩ := List.mem_map.mp hi
      obtain ⟨hj, hk⟩ := mem_runEdgeOccurrences.mp hjk
      have r := runLength_spec hlv hj
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ (by have := r.start_lt; omega)),
        decide_eq_true (r.edge_upper hlv hk)⟩
    · intro hi
      obtain ⟨hi, ht⟩ := List.mem_filter.mp hi
      obtain ⟨j, hj, k, hk, he⟩ := edge_has_run hh hlv hbot (List.mem_range.mp hi) (of_decide_eq_true ht)
      exact List.mem_map.mpr ⟨(j, k), mem_runEdgeOccurrences.mpr ⟨hj, hk⟩, he⟩
  · apply nodup_map_on _ (runEdgeOccurrences_nodup P w t)
    rintro ⟨i, k⟩ hik ⟨j, l⟩ hjl he
    obtain ⟨hi, hk⟩ := mem_runEdgeOccurrences.mp hik
    obtain ⟨hj, hl⟩ := mem_runEdgeOccurrences.mp hjl
    obtain ⟨rfl, rfl⟩ := run_edge_unique (runLength_spec hlv hi) (runLength_spec hlv hj) hk hl he
    rfl

private theorem sum_perm {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b xs => simp [Int.add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem sum_flatMap {A B : Type} (xs : List A) (f : A -> List B) (g : B -> Int) :
    ((xs.flatMap f).map g).sum = (xs.map (fun a => ((f a).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_filter {A : Type} (xs : List A) (p : A -> Bool) (f : A -> Int) :
    ((xs.filter p).map f).sum = (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

private theorem sum_natCast (xs : List Nat) : (xs.map (fun n : Nat => (n : Int))).sum = (xs.sum : Int) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The edge-occurrence bijection really gives the total upper length. -/
theorem sum_runLength_eq_upperLength {P : Nat} {w : Nat -> Bool} {t : Int}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hbot : botLayer P w <= t) :
    ((runStarts P w t).map (fun i => (runLength P w t i : Int))).sum = upperLength P w t := by
  have he := (runEdgeOccurrence_perm hh hlv hbot).length_eq
  simp only [List.length_map, runEdgeOccurrences, List.length_flatMap,
    List.length_range] at he
  rw [upperLength_eq_count, <- he]
  have hs := sum_natCast ((runStarts P w t).map (runLength P w t))
  simpa only [List.map_map, Function.comp_def] using hs

private theorem sum_differences (f : Nat -> Int) (n : Nat) :
    ((List.range n).map (fun k => f (k + 1) - f k)).sum = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; omega

private theorem path_stepX {P len : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) {k : Nat} (hk : k < len) :
    (p.pos w (k + 1)).1 - (p.pos w k).1 = stepX w (p.phase k) := by
  rw [p.pos_step hk]
  change (move (p.pos w k) (outDir w (p.phase k))).1 - (p.pos w k).1 = _
  cases ho : outDir w (p.phase k) <;> simp [stepX, ho, move] <;> omega

/-- The sum is over physical horizontal displacement, including the seam carry. -/
def runTransport (P : Nat) (w : Nat -> Bool) (t : Int) : Int :=
  ((runStarts P w t).map (fun i => (runEndPos P w t i).1 - (wordPos w i).1)).sum

/-- Actual run displacement is the sum of its actual departing edge displacements. -/
theorem run_displacement_eq_steps {P i : Nat} {w : Nat -> Bool} {t : Int}
    (hi : i < P) :
    (runEndPos P w t i).1 - (wordPos w i).1 =
      ((List.range (runLength P w t i)).map (fun k => stepX w (phase P i k))).sum := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i (runLength P w t i)
  have he := sum_differences (fun k => (p.pos w k).1) (runLength P w t i)
  have hs : ((List.range (runLength P w t i)).map
      (fun k => (p.pos w (k + 1)).1 - (p.pos w k).1)).sum =
      ((List.range (runLength P w t i)).map (fun k => stepX w (phase P i k))).sum := by
    apply sum_congr
    intro k hk
    exact path_stepX p (List.mem_range.mp hk)
  rw [hs, ofStart_pos_zero hi] at he
  exact he.symm

theorem runTransport_eq_upperTransport {P : Nat} {w : Nat -> Bool} {t : Int}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hbot : botLayer P w <= t) : runTransport P w t = upperTransport P w t := by
  have he := sum_perm ((runEdgeOccurrence_perm hh hlv hbot).map (stepX w))
  simp only [List.map_map, Function.comp_def] at he
  rw [runEdgeOccurrences, sum_flatMap] at he
  simp only [List.map_map, Function.comp_def] at he
  rw [sum_filter] at he
  unfold runTransport upperTransport
  calc
    _ = ((runStarts P w t).map (fun i =>
        ((List.range (runLength P w t i)).map (fun k => stepX w (phase P i k))).sum)).sum := by
      apply sum_congr
      intro i hi
      exact run_displacement_eq_steps (mem_runStarts.mp hi).1
    _ = _ := by
      rw [he]
      apply sum_congr
      intro i _
      by_cases ht : t <= edgeCut w i <;> simp [upperWeight, ht]

/-- Round 33, equation (33.2), for the actual upper runs, with sigma=+1.
The required lower support bound prevents a missing boundary-free full cycle. -/
theorem runTransport_eq_signed_cut_sum {P : Nat} {w : Nat -> Bool} {t : Int}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hbot : botLayer P w <= t) :
    runTransport P w t = sumAbove P w t (fun s => cutSign s * (cutFlow P w s : Int)) := by
  rw [runTransport_eq_upperTransport hh hlv hbot, upperTransport_eq_signed_sum_cutFlow hlv]

/-- Round 36's length sum follows from the actual run-edge bijection. -/
theorem sum_runLength_eq_twice_cut_sum {P : Nat} {w : Nat -> Bool} {t : Int}
    (hh : (wordTrace w P).2 = .north) (hlv : layer (wordDrift P w) = 0)
    (hbot : botLayer P w <= t) :
    ((runStarts P w t).map (fun i => (runLength P w t i : Int))).sum =
      2 * sumAbove P w t (fun s => (cutFlow P w s : Int)) := by
  rw [sum_runLength_eq_upperLength hh hlv hbot, upperLength_eq_twice_sum_cutFlow hlv]

/-- Round 40: equal endpoint phases in a full-period run have zero stable-time
difference, so a strict rank decrease must not be asserted for this case. -/
theorem UpperRun.full_period_stableTime {P i : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i P) :
    Drift.stableTime (2, -2) P w (phase P i P) - Drift.stableTime (2, -2) P w i = 0 /\
      Drift.stableRank P w (phase P i P) = Drift.stableRank P w i := by
  rw [r.full_period_end, Int.sub_self]
  exact ⟨rfl, rfl⟩

/-- Round 40: a same-physical-cell return really is short, although a general
upper excursion need not be. Nonzero full drift supplies the missing premise. -/
theorem UpperRun.physical_return_short {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : UpperRun P w t i len) (hP : 0 < P) (hd : wordDrift P w = (2, -2))
    (hret : (ContinuousPhasePath.ofStart hP i len).pos w len =
      (ContinuousPhasePath.ofStart hP i len).pos w 0) : len < P := by
  have he := Drift.path_return_phase_ne (ContinuousPhasePath.ofStart hP i len)
    hd drift_two_negTwo_ne_zero r.length_pos hret
  change phase P i len ≠ phase P i 0 at he
  by_cases hl : len < P
  · exact hl
  · have hlen : len = P := by have := r.length_le; omega
    rw [hlen, phase_period r.start_lt, phase_zero r.start_lt] at he
    exact False.elim (he rfl)

/-- The eight-step geometric control from round 40. It is not asserted consistent. -/
def fullPeriodControl (i : Nat) : Bool :=
  ([false, false, true, false, true, false, false, false] : List Bool)[i]?.getD false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem fullPeriodControl_data :
    (wordTrace fullPeriodControl 8).2 = .north /\
    wordDrift 8 fullPeriodControl = (2, -2) /\
    7 ∈ runStarts 8 fullPeriodControl (-1) /\
    runLength 8 fullPeriodControl (-1) 7 = 8 /\
    runEndPos 8 fullPeriodControl (-1) 7 = addPoint (wordPos fullPeriodControl 7) (2, -2) := by
  decide +kernel

/-- A real geometric full-period excursion, with equal phases and unequal physical endpoints. -/
theorem fullPeriodControl_run : UpperRun 8 fullPeriodControl (-1) 7 8 := by
  obtain ⟨_, hd, hi, hl, _⟩ := fullPeriodControl_data
  have hr := runLength_spec (show layer (wordDrift 8 fullPeriodControl) = 0 by rw [hd]; rfl) hi
  rw [hl] at hr
  exact hr

set_option maxRecDepth 10000 in
/-- The full-period control only refutes the erroneous geometric L<P argument. -/
theorem fullPeriodControl_not_consistent : Not (ConsistentWord 8 fullPeriodControl) := by
  have hf : fullPeriodControl 4 = true /\ Drift.stableRank 8 fullPeriodControl 4 = 0 := by
    decide +kernel
  intro h
  have hc := Drift.consistentWord_stableRank_color h (i := 4) (by decide)
  rw [hf.1, hf.2] at hc
  contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Kernel-checked data from the actual standard word, not a synthetic port table. -/
theorem stdHighwaySE_defect_data :
    BB 104 stdHighwaySE 4 = 2 /\ BT 104 stdHighwaySE 4 = 3 /\
    TB 104 stdHighwaySE 4 = 3 /\ TT 104 stdHighwaySE 4 = 1 /\
    returnCount 104 stdHighwaySE 4 = 2 /\ nonreturnCount 104 stdHighwaySE 4 = 7 /\
    nonreturnCount 104 stdHighwaySE 5 = 6 /\
    runTransport 104 stdHighwaySE 4 = 2 /\ runTransport 104 stdHighwaySE 5 = -7 /\
    secondMoment 104 stdHighwaySE 4 = 168 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Concrete counterexample to omitting the lower-support hypothesis in the
run-edge covering or signed run-transport identity. -/
theorem stdHighwaySE_below_support :
    botLayer 104 stdHighwaySE = -1 /\
    runStarts 104 stdHighwaySE (-2) = [] /\
    upperLength 104 stdHighwaySE (-2) = 104 /\
    runTransport 104 stdHighwaySE (-2) = 0 /\
    upperTransport 104 stdHighwaySE (-2) = 2 := by
  decide +kernel

/-- A consistent word with the required full drift instantiates the new results. -/
theorem stdHighwaySE_nonvacuous :
    ConsistentWord 104 stdHighwaySE /\ wordDrift 104 stdHighwaySE = (2, -2) /\
    runDefect 104 stdHighwaySE 4 = 1 /\ secondMoment 104 stdHighwaySE 4 = 168 /\
    runTransport 104 stdHighwaySE 5 < 0 := by
  obtain ⟨hbb, _, _, htt, _, _, _, _, ht, hk⟩ := stdHighwaySE_defect_data
  refine ⟨stdHighwaySE_consistent, stdHighwaySE_drift, ?_, hk, by omega⟩
  unfold runDefect
  rw [hbb, htt]
  decide

end LangtonsAnt.WidthDefects
