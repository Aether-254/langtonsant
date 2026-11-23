import DiagonalMultipleLanes

/-!
# Rank-zero lane: verified local reduction and standard-word witness

This file does not claim the general rank-zero-lane existence theorem.
The missing global steps are the geometric winding identity and the period
bound derived from consistency. Neither is postulated here for a word theorem.
`early_of_negative_sum` isolates only the elementary finite-sum argument.
-/

namespace LangtonsAnt.DiagonalRankZeroLane

open DiagonalMultipleLanes

/-- Every top translation class is visited. Integer lane indices avoid choosing
representatives; periodicity makes this equivalent to testing `0 <= r < m`. -/
def TopOccupied (m P : Nat) (w : Nat → Bool) : Prop :=
  ∀ r : Int, (Drift.classPhases (diagDrift m) P w
    (laneCell (topLayer P w) r)).length ≠ 0

theorem top_occupied_length_one {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w) r)).length = 1 := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_diagDrift m
  have hb := TwoCellDiagonal.topLayer_class_length_le_one_of_layer_zero h hlv
    (c := laneCell (topLayer P w) r) (layer_laneCell _ _)
  rw [hd] at hb
  have hn := ht r
  omega

theorem first_inner_candidates {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    IsFirstInnerWord (laneAlpha m P w (topLayer P w - 1) r) :=
  firstInner_of_top_occupied h hm hd r (ht r) (ht (r + 1))

/-- Unique upper arrival and departure, expressed as lists of their ranks.
The first alternative is exactly the desired early-lane alternative. -/
theorem first_inner_port_ranks {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    let a := laneAlpha m P w (topLayer P w - 1) r
    let b := laneBeta m P w (topLayer P w - 1) r
    ((a = word100 ∨ a = word1000) ∧
      UnitDiagonal.trueIdx a = [0] ∧ UnitDiagonal.trueIdx b = [2]) ∨
    ((a = word001 ∨ a = word0010) ∧
      UnitDiagonal.trueIdx a = [2] ∧ UnitDiagonal.trueIdx b = [0]) := by
  dsimp only
  rw [laneBeta_depth1 h hm hd r]
  rcases first_inner_candidates h hm hd ht r with ha | ha | ha | ha
  · rw [ha]; exact Or.inl ⟨Or.inl rfl, by decide, by decide⟩
  · rw [ha]; exact Or.inl ⟨Or.inr rfl, by decide, by decide⟩
  · rw [ha]; exact Or.inr ⟨Or.inl rfl, by decide, by decide⟩
  · rw [ha]; exact Or.inr ⟨Or.inr rfl, by decide, by decide⟩

/-- Strict within-class ordering at ranks zero and two. No comparison between
different lanes occurs in this lemma. -/
theorem rank_zero_time_lt_rank_two {m P : Nat} {w : Nat → Bool}
    (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (c : Point)
    (hlen : 2 < (Drift.classPhases (diagDrift m) P w c).length) :
    Drift.stableTime (diagDrift m) P w (classPhaseAtRank (diagDrift m) P w c 0) <
      Drift.stableTime (diagDrift m) P w (classPhaseAtRank (diagDrift m) P w c 2) := by
  have hv := diagDrift_ne_zero hm
  obtain ⟨h0, hr0⟩ := classPhaseAtRank_spec hd hv (show 0 <
    (Drift.classPhases (diagDrift m) P w c).length by omega)
  obtain ⟨h2, hr2⟩ := classPhaseAtRank_spec hd hv hlen
  obtain ⟨h0P, h0c⟩ := Drift.mem_classPhases.mp h0
  obtain ⟨h2P, h2c⟩ := Drift.mem_classPhases.mp h2
  exact (Drift.stableRank_lt_iff_stableTime_lt hd hv h0P h2P
    (h0c.trans h2c.symm)).mp (by omega)

private theorem sum_nonneg (xs : List Nat) (f : Nat → Int)
    (h : ∀ r ∈ xs, 0 ≤ f r) : 0 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have hs := ih (fun r hr => h r (by simp [hr]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Pure finite-sum obstruction. This is not the geometric winding identity:
`delta` is arbitrary, and the negative sum must be supplied explicitly. -/
theorem early_of_negative_sum (m : Nat) (early : Nat → Prop) (delta : Nat → Int)
    (hlate : ∀ r < m, ¬ early r → 0 ≤ delta r)
    (hsum : ((List.range m).map delta).sum < 0) :
    ∃ r, r < m ∧ early r := by
  classical
  apply Classical.byContradiction
  intro hn
  have hp : ∀ r ∈ List.range m, 0 ≤ delta r := by
    intro r hr
    have hrm := List.mem_range.mp hr
    exact hlate r hrm (fun he => hn ⟨r, hrm, he⟩)
  have := sum_nonneg (List.range m) delta hp
  omega

/-! ## A genuine consistent word with both kinds of lane -/

theorem standard_top_classes :
    Drift.classPhases (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE (laneCell 9 0) = [59] ∧
    Drift.classPhases (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE (laneCell 9 1) = [41] := by
  decide +kernel

theorem standard_top_occupied : TopOccupied 2 104 TwoCellDiagonal.stdHighwaySE := by
  intro r
  rw [TwoCellDiagonal.stdHighwaySE_topLayer]
  have hr : r % (2 : Int) = 0 ∨ r % (2 : Int) = 1 := by omega
  rcases hr with hr | hr
  · have hc : Drift.SameClass (diagDrift 2) (laneCell 9 r) (laneCell 9 0) :=
      (sameClass_laneCell_iff (by decide) 9 r 9 0).mpr ⟨rfl, by omega⟩
    rw [Drift.classPhases_congr 104 _ hc, standard_top_classes.1]
    decide
  · have hc : Drift.SameClass (diagDrift 2) (laneCell 9 r) (laneCell 9 1) :=
      (sameClass_laneCell_iff (by decide) 9 r 9 1).mpr ⟨rfl, by omega⟩
    rw [Drift.classPhases_congr 104 _ hc, standard_top_classes.2]
    decide

theorem standard_lane_words :
    laneAlpha 2 104 TwoCellDiagonal.stdHighwaySE 8 0 = word001 ∧
    laneAlpha 2 104 TwoCellDiagonal.stdHighwaySE 8 1 = word1000 := by
  set_option maxRecDepth 100000 in
    decide +kernel

/-- The paper's actual port phases, including the rank-zero upper arrival
at phase 42 and rank-two upper departure at phase 58 in lane one. -/
theorem standard_port_phases :
    classPhaseAtRank (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE (laneCell 8 0) 2 = 60 ∧
    classPhaseAtRank (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE (laneCell 8 0) 0 = 40 ∧
    classPhaseAtRank (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE (laneCell 8 1) 0 = 42 ∧
    classPhaseAtRank (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE (laneCell 8 1) 2 = 58 := by
  set_option maxRecDepth 100000 in
    decide +kernel

theorem standard_winding_values :
    Drift.stableTime (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE 60 -
      Drift.stableTime (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE 40 = 20 ∧
    Drift.stableTime (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE 42 -
      Drift.stableTime (diagDrift 2) 104 TwoCellDiagonal.stdHighwaySE 58 = -120 ∧
    (20 : Int) + (-120) = 2 * 2 - 104 := by
  decide +kernel

theorem standard_rank_zero_witness :
    ConsistentWord 104 TwoCellDiagonal.stdHighwaySE ∧
    wordDrift 104 TwoCellDiagonal.stdHighwaySE = diagDrift 2 ∧
    TopOccupied 2 104 TwoCellDiagonal.stdHighwaySE ∧
    2 * 2 < (104 : Nat) ∧
    laneAlpha 2 104 TwoCellDiagonal.stdHighwaySE
      (topLayer 104 TwoCellDiagonal.stdHighwaySE - 1) 1 = word1000 := by
  refine ⟨TwoCellDiagonal.stdHighwaySE_consistent, TwoCellDiagonal.stdHighwaySE_drift,
    standard_top_occupied, by decide, ?_⟩
  rw [TwoCellDiagonal.stdHighwaySE_topLayer]
  exact standard_lane_words.2

end LangtonsAnt.DiagonalRankZeroLane
