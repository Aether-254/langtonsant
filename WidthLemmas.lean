import DiagonalMultipleLanes

/-!
Common time and rank-gap identities for full drift `(2,-2)`.

Source: research/persist-A-width-2026-11-22.md, rounds 36 and 37.
`eta` is defined on the actual word geometry.  Its relation to `stableTime`
retains the lane-dependent offset.  The path identity allows arbitrary lengths,
including an entire period and paths crossing any number of period seams.

The rank-gap expansion uses the actual class phases and arrival/departure ports.
No sign is imposed on the charge prefixes, and the final boundary term is kept.
This file does not assert a uniform width bound or the excursion-counting and
upper-region flow identities from rounds 33--36.
-/

namespace LangtonsAnt.WidthLemmas

open TwoCellDiagonal DiagonalMultipleLanes

/-- One time coordinate for both lanes, in the original word frame. -/
def eta (P : Nat) (w : Nat -> Bool) (i : Nat) : Int :=
  2 * (i : Int) - (P : Int) * (wordPos w i).1

/-- Round 36: the offset between `eta` and twice stable time must be retained. -/
theorem eta_eq_stableTime (P : Nat) (w : Nat -> Bool) (i : Nat) :
    eta P w i = 2 * Drift.stableTime (2, -2) P w i -
      (P : Int) * ((wordPos w i).1 % 2) := by
  have hx : (wordPos w i).1 =
      2 * ((wordPos w i).1 / 2) + (wordPos w i).1 % 2 := by omega
  have hm := congrArg (fun x : Int => (P : Int) * x) hx
  simp only [Int.mul_add] at hm
  rw [Int.mul_left_comm (P : Int) 2] at hm
  unfold eta Drift.stableTime Drift.lift
  simp only [show Not ((2 : Int) = 0) by decide, ite_false]
  rw [Int.mul_sub]
  omega

/-- The common coordinate is unchanged by any integer period lift. -/
theorem eta_lift_invariant {P : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (2, -2)) (k : Int) (i : Nat) :
    2 * (k * (P : Int) + (i : Int)) -
      (P : Int) * (biPeriodicPos P w k i).1 = eta P w i := by
  simp only [biPeriodicPos, hd, addPoint, scalePoint, eta, Int.mul_add,
    Int.mul_comm k 2, Int.mul_comm k (P : Int)]
  rw [Int.mul_left_comm (P : Int) 2 k]
  omega

/-- Round 36: exact endpoint difference, without a same-lane or short-path assumption. -/
theorem path_eta_difference {P len : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = (2, -2)) :
    eta P w (p.phase len) - eta P w (p.phase 0) =
      2 * (len : Int) - (P : Int) * ((p.pos w len).1 - (p.pos w 0).1) := by
  have h0 := eta_lift_invariant hd (p.period 0) (p.phase 0)
  have h1 := eta_lift_invariant hd (p.period len) (p.phase len)
  have ht := p.time_eq (Nat.le_refl len)
  change 2 * (p.period 0 * (P : Int) + (p.phase 0 : Int)) -
    (P : Int) * (p.pos w 0).1 = _ at h0
  change 2 * (p.period len * (P : Int) + (p.phase len : Int)) -
    (P : Int) * (p.pos w len).1 = _ at h1
  rw [Int.mul_sub]
  omega

/-- Within a translation class the lane offsets cancel exactly. -/
theorem eta_difference_eq_twice_stableTime {P : Nat} {w : Nat -> Bool} {i j : Nat}
    (hc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j)) :
    eta P w j - eta P w i =
      2 * (Drift.stableTime (2, -2) P w j - Drift.stableTime (2, -2) P w i) := by
  have hlane := ((sameClass_two_negTwo_iff _ _).mp hc).2
  have hm : (wordPos w i).1 % 2 = (wordPos w j).1 % 2 := by
    unfold lane at hlane
    have he := Bool.eq_iff_iff.mp hlane
    simp only [decide_eq_true_eq] at he
    omega
  rw [eta_eq_stableTime, eta_eq_stableTime, hm, Int.mul_sub]
  omega

/-- `eta` induces precisely the actual stable-rank order within each class. -/
theorem eta_lt_iff_rank_lt {P i j : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (2, -2)) (hi : i < P) (hj : j < P)
    (hc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j)) :
    eta P w i < eta P w j <-> Drift.stableRank P w i < Drift.stableRank P w j := by
  have ht := eta_difference_eq_twice_stableTime (P := P) hc
  have hr := Drift.stableRank_lt_iff_stableTime_lt hd drift_two_negTwo_ne_zero hi hj hc
  omega

private theorem wordPos_x_parity (w : Nat -> Bool) (n : Nat) :
    ((wordPos w n).1 - (((n + 1) / 2 : Nat) : Int)) % 2 = 0 := by
  induction n with
  | zero => simp [wordPos, wordTrace]
  | succ n ih =>
    have hax := wordTrace_axis w n
    have hpos : wordPos w (n + 1) =
        move (wordPos w n) (turn (w n) (wordTrace w n).2) := rfl
    rw [hpos]
    cases hd' : (wordTrace w n).2 <;> rw [hd'] at hax <;> cases w n <;>
      simp only [Direction.horizontal, turn, Direction.left, Direction.right, move,
        Bool.false_eq_true, ite_true, ite_false] at hax ⊢
    all_goals
      try (have hodd : n % 2 = 1 := of_decide_eq_true hax.symm; omega)
      try (have hev : Not (n % 2 = 1) := by
            intro ho; rw [ho] at hax; simp at hax
           omega)

private theorem sameClass_phase_mod_four {w : Nat -> Bool} {i j : Nat}
    (hc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j)) :
    (i : Int) % 4 = (j : Int) % 4 := by
  obtain ⟨hl, hr⟩ := (sameClass_two_negTwo_iff _ _).mp hc
  have hpi := layer_wordPos_parity w i
  have hpj := layer_wordPos_parity w j
  have hxi := wordPos_x_parity w i
  have hxj := wordPos_x_parity w j
  unfold lane at hr
  have he := Bool.eq_iff_iff.mp hr
  simp only [decide_eq_true_eq] at he
  omega

/-- Round 37: every positive same-class time gap is a positive multiple of eight. -/
theorem eta_gap_pos_multiple_eight {P i j : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i < P) (hj : j < P)
    (hc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j))
    (hr : Drift.stableRank P w i < Drift.stableRank P w j) :
    exists q : Int, 0 < q /\ eta P w j - eta P w i = 8 * q := by
  have hpos := (eta_lt_iff_rank_lt hd hi hj hc).mpr hr
  have ht := eta_difference_eq_twice_stableTime (P := P) hc
  have hp : (P : Int) % 4 = 0 := by
    exact_mod_cast period_mod_four_eq_zero h hd
  have hij := sameClass_phase_mod_four hc
  have hm (k : Nat) : ((P : Int) * Drift.lift (2, -2) (wordPos w k)) % 4 = 0 := by
    rw [Int.mul_emod, hp]
    simp
  have hmi := hm i
  have hmj := hm j
  unfold Drift.stableTime at ht
  refine ⟨(eta P w j - eta P w i) / 8, ?_, ?_⟩ <;> omega

/-- At least eight, with no asserted upper bound by one or two periods. -/
theorem eta_gap_ge_eight {P i j : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i < P) (hj : j < P)
    (hc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j))
    (hr : Drift.stableRank P w i < Drift.stableRank P w j) :
    8 <= eta P w j - eta P w i := by
  obtain ⟨q, hq, he⟩ := eta_gap_pos_multiple_eight h hd hi hj hc hr
  omega

/-- Downward through events have charge `1`, upward through events `-1`;
both kinds of bounce have charge `0`. -/
def throughCharge (w : Nat -> Bool) (i : Nat) : Int :=
  (if alpha w i then 1 else 0) - (if beta w i then 1 else 0)

/-- Lookup in the repository's actual stable-rank enumeration. -/
abbrev rankPhase (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool) (k : Nat) : Nat :=
  classPhaseAtRank (2, -2) P w (classRep t r) k

def rankEta (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool) (k : Nat) : Int :=
  eta P w (rankPhase P w t r k)

def rankCharge (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool) (k : Nat) : Int :=
  throughCharge w (rankPhase P w t r k)

/-- Charge of the first `n` actual ranks; the paper's `S_j` is `chargePrefix (j+1)`. -/
def chargePrefix (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool) (n : Nat) : Int :=
  ((List.range n).map (rankCharge P w t r)).sum

/-- The lane's signed boundary time, over actual phase occurrences. -/
def classBoundaryTime (P : Nat) (w : Nat -> Bool) (t : Int) (r : Bool) : Int :=
  ((classPhases2 P w t r).map (fun i => throughCharge w i * eta P w i)).sum

private theorem sum_range_succ (f : Nat -> Int) (n : Nat) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp [List.range_succ, List.sum_append]

private theorem summation_by_parts (a e : Nat -> Int) (n : Nat) :
    ((List.range (n + 1)).map (fun k => a k * e k)).sum =
      ((List.range (n + 1)).map a).sum * e n -
        ((List.range n).map (fun j =>
          ((List.range (j + 1)).map a).sum * (e (j + 1) - e j))).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ (fun k => a k * e k) (n + 1),
      sum_range_succ a (n + 1),
      sum_range_succ (fun j =>
        ((List.range (j + 1)).map a).sum * (e (j + 1) - e j)) n, ih]
    simp only [Int.add_mul, Int.mul_sub]
    omega

private theorem sum_int_perm {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b xs => simp [Int.add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem class_sum_ranked {P : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool) (f : Nat -> Int) :
    ((classPhases2 P w t r).map f).sum =
      ((List.range (classMult P w t r)).map (fun k => f (rankPhase P w t r k))).sum := by
  have he := sum_int_perm ((classRankedPhases_perm (c := classRep t r) hd
    drift_two_negTwo_ne_zero).map f)
  simpa only [classRankedPhases, List.map_map, Function.comp_def,
    classMult, classPhases2, rankPhase] using he.symm

/-- Round 37, equation (37.1), for the actual class and through-event charges.
Neither prefix signs nor a vanishing final prefix are assumed. -/
theorem boundary_rank_gap_expansion {P : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool)
    (hm : 0 < classMult P w t r) :
    classBoundaryTime P w t r =
      chargePrefix P w t r (classMult P w t r) *
        rankEta P w t r (classMult P w t r - 1) -
      ((List.range (classMult P w t r - 1)).map (fun j =>
        chargePrefix P w t r (j + 1) *
          (rankEta P w t r (j + 1) - rankEta P w t r j))).sum := by
  unfold classBoundaryTime
  rw [class_sum_ranked hd]
  have he := summation_by_parts (rankCharge P w t r) (rankEta P w t r)
    (classMult P w t r - 1)
  rw [show classMult P w t r - 1 + 1 = classMult P w t r by omega] at he
  exact he

/-- The gaps appearing in the expansion are positive multiples of eight. -/
theorem adjacent_rankEta_gap {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (t : Int) (r : Bool) {k : Nat} (hk : k + 1 < classMult P w t r) :
    exists q : Int, 0 < q /\
      rankEta P w t r (k + 1) - rankEta P w t r k = 8 * q := by
  have h0 := classPhaseAtRank_spec hd drift_two_negTwo_ne_zero
    (c := classRep t r) (k := k) (show k < classMult P w t r by omega)
  have h1 := classPhaseAtRank_spec hd drift_two_negTwo_ne_zero
    (c := classRep t r) (k := k + 1) hk
  obtain ⟨hi, hic⟩ := Drift.mem_classPhases.mp h0.1
  obtain ⟨hj, hjc⟩ := Drift.mem_classPhases.mp h1.1
  apply eta_gap_pos_multiple_eight h hd hi hj (hic.trans hjc.symm)
  change Drift.stableRank P w (classPhaseAtRank (2, -2) P w (classRep t r) k) <
    Drift.stableRank P w (classPhaseAtRank (2, -2) P w (classRep t r) (k + 1))
  rw [h0.2, h1.2]
  omega

private theorem throughCharge_sum (w : Nat -> Bool) (xs : List Nat) :
    (xs.map (throughCharge w)).sum =
      ((xs.filter (fun i => decide (inDir w i = .south))).length : Int) +
      ((xs.filter (fun i => decide (inDir w i = .west))).length : Int) -
      ((xs.filter (fun i => decide (outDir w i = .east))).length : Int) -
      ((xs.filter (fun i => decide (outDir w i = .north))).length : Int) := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    cases ha : inDir w i <;> cases hb : outDir w i <;>
      simp [throughCharge, alpha, beta, ha, hb, ih] <;> omega

/-- The last charge prefix in (37.1) is an actual imbalance of boundary ports.
It need not vanish in either lane separately. -/
theorem chargePrefix_full_eq_counts {P : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    (t : Int) (r : Bool) :
    chargePrefix P w t r (classMult P w t r) =
      (sCnt P w (t + 1) r : Int) + (wCnt P w (t + 1) (!r) : Int) -
      (eCnt P w t r : Int) - (nCnt P w t r : Int) := by
  have hs := depCount_eq_arrCount_south hh hd (t := t + 1) r
  have hw := depCount_eq_arrCount_west hh hd (t := t + 1) (!r)
  have ht : t + 1 - 1 = t := by omega
  rw [ht] at hs
  rw [ht, Bool.not_not] at hw
  unfold chargePrefix rankCharge
  rw [← class_sum_ranked hd t r (throughCharge w), throughCharge_sum, hs, hw]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Concrete checks from round 37: mixed prefix signs, nonzero per-lane end
charges, and a gap larger than twice the full period. -/
theorem stdHighwaySE_rank_data :
    classMult 104 stdHighwaySE 4 true = 7 /\
    chargePrefix 104 stdHighwaySE 4 true 1 = 1 /\
    chargePrefix 104 stdHighwaySE 4 true 5 = -1 /\
    classMult 104 stdHighwaySE 6 false = 6 /\
    classMult 104 stdHighwaySE 6 true = 6 /\
    chargePrefix 104 stdHighwaySE 6 false 6 = 3 /\
    chargePrefix 104 stdHighwaySE 6 true 6 = -3 /\
    rankEta 104 stdHighwaySE 6 true 3 - rankEta 104 stdHighwaySE 6 true 2 = 232 := by
  decide +kernel

/-- The real standard word satisfies the hypotheses and has an adjacent gap
`232 > 2*104`.  No period-sized gap upper bound is available from these lemmas. -/
theorem stdHighwaySE_nonvacuous :
    ConsistentWord 104 stdHighwaySE /\ wordDrift 104 stdHighwaySE = (2, -2) /\
    2 + 1 < classMult 104 stdHighwaySE 6 true /\
    2 * (104 : Int) < rankEta 104 stdHighwaySE 6 true 3 -
      rankEta 104 stdHighwaySE 6 true 2 := by
  obtain ⟨_, _, _, _, hm, _, _, hgap⟩ := stdHighwaySE_rank_data
  exact ⟨stdHighwaySE_consistent, stdHighwaySE_drift, by omega, by omega⟩

end LangtonsAnt.WidthLemmas
