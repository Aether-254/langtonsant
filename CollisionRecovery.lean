import SingleFlipReduction

namespace LangtonsAnt

/-- This immediate collision leaves a genuinely blank board after one update. -/
theorem singleBlack_origin_step : step (singleBlack (0, 0)) = whiteAt (-1, 0) .west := by
  have hb : flip (fun q : Point => decide (q = (0, 0))) (0, 0) = fun _ => false := by
    funext q
    by_cases hq : q = (0, 0) <;> simp [flip, hq]
  simp [step, singleBlack, turn, Direction.left, move, whiteAt, hb]

theorem singleBlack_origin_standard : StandardHighwayFrom (singleBlack (0, 0)) 12081 (2, -2) := by
  have h := whiteAt_standard (-1, 0) .west
  rw [← singleBlack_origin_step] at h
  change StandardHighwayFrom (run (singleBlack (0, 0)) 1) 12080 (2, -2) at h
  exact h.of_run

/-- The seed with the ant's initially black cell turned white. -/
def flippedHighwaySeed : FiniteState :=
  { highwaySeed with black := toggleCells highwaySeed.black highwaySeed.pos }

theorem flippedHighwaySeed_toState :
    flippedHighwaySeed.toState = flipCell highwaySeed.toState highwaySeed.toState.pos :=
  highwaySeed.toState_flip highwaySeed.pos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem flippedHighwaySeed_entry_check :
    checkAgreement (-4) (flippedHighwaySeed.run 276) (highwaySeed.translate (-2, -2)) = true := by
  decide +kernel

theorem flippedHighwaySeed_entry :
    AgreesBelow (-4) (run flippedHighwaySeed.toState 276)
      (translate (-2, -2) highwaySeed.toState) := by
  have h := checkAgreement_sound flippedHighwaySeed_entry_check
  simpa only [FiniteState.toState_run, FiniteState.toState_translate] using h

theorem flippedHighwaySeed_standard :
    StandardHighwayFrom flippedHighwaySeed.toState 276 (-2, -2) := by
  apply standard_highway_of_entry (-2, -2)
  rw [show weight ((-2, -2) : Point) = -4 by decide]
  exact flippedHighwaySeed_entry

/-- A concrete collision-recovery theorem, not the universal flip-stability assertion. -/
theorem standard_seed_flip_recovers :
    StandardHighwayFrom (flipCell highwaySeed.toState highwaySeed.toState.pos) 276 (-2, -2) := by
  rw [← flippedHighwaySeed_toState]
  exact flippedHighwaySeed_standard

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem flippedHighwaySeed_bound_check : checkBounded 7 276 flippedHighwaySeed = true := by
  decide +kernel

theorem flippedHighwaySeed_all_bounded (n : Nat) :
    weight (run flippedHighwaySeed.toState n).pos <= 7 := by
  by_cases hn : n < 276
  · exact checkBounded_sound flippedHighwaySeed_bound_check n hn
  · have hc := highwaySeed_certificate.translate (-2, -2)
    have he : AgreesBelow (0 + weight (-2, -2)) (run flippedHighwaySeed.toState 276)
        (translate (-2, -2) highwaySeed.toState) := flippedHighwaySeed_entry
    have hm := hc.matches_forever he (n - 276)
    have hb := hc.all_bounded (n - 276)
    rw [← hm.pos, ← run_add] at hb
    have heq : 276 + (n - 276) = n := by omega
    rw [heq] at hb
    change weight (run flippedHighwaySeed.toState n).pos <= -4 at hb
    omega

/-- Arbitrary changes outside the recovery region cannot affect this collision and its tail. -/
theorem standard_of_flippedSeed_match {s : State}
    (h : AgreesBelow 7 s flippedHighwaySeed.toState) : StandardHighwayFrom s 276 (-2, -2) :=
  flippedHighwaySeed_standard.of_agreesBelow h flippedHighwaySeed_all_bounded

/-- A proved infinite family of current-cell flips; the extra strip through weight seven matters. -/
theorem standard_seed_flip_recovers_of_matches {s : State}
    (h : AgreesBelow 7 s highwaySeed.toState) :
    StandardHighwayFrom (flipCell s s.pos) 276 (-2, -2) := by
  apply standard_of_flippedSeed_match
  rw [flippedHighwaySeed_toState, h.pos, flipCell_eq_perturb, flipCell_eq_perturb]
  exact h.perturb (fun q => decide (q = highwaySeed.toState.pos))

/-- Rotate the one-cell example so its eventual highway points southwest. -/
def packedSingleEastRotated : PackedState := ⟨2 ^ bitIndex (0, 1), (0, 0), .west⟩

theorem packedSingleEastRotated_toState :
    packedSingleEastRotated.toState = rotateState .west (singleBlack (1, 0)) := by
  have hzero : packedBoard 0 = fun _ => false := by
    funext q
    simp [packedBoard]
  have hb := packedBoard_flip 0 (0, 1) (by decide)
  rw [Nat.zero_xor, hzero] at hb
  have hc : flip (fun _ => false) (0, 1) =
      fun q => decide (rotatePoint .east q = (1, 0)) := by
    funext q
    have heq : rotatePoint .east q = (1, 0) ↔ q = (0, 1) := by
      cases q
      simp only [rotatePoint, Prod.mk.injEq]
      omega
    simp [flip, heq]
  simp only [PackedState.toState, packedSingleEastRotated, hb, hc,
    rotateState, singleBlack, inverseRotation, rotatePoint, rotateDir, Direction.left]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem singleBlack_east_entry_check :
    checkPackedEntry 2905 packedSingleEastRotated (-23)
      (highwaySeed.translate (-16, -7)) = true := by
  decide +kernel

/-- This black cell is encountered at time one and changes the eventual drift direction. -/
theorem singleBlack_east_standard : StandardHighwayFrom (singleBlack (1, 0)) 2905 (-2, 2) := by
  have he := checkPackedEntry_sound singleBlack_east_entry_check
  rw [packedSingleEastRotated_toState, FiniteState.toState_translate] at he
  have hs : StandardHighwayFrom (rotateState .west (singleBlack (1, 0))) 2905 (-2, -2) := by
    apply standard_highway_of_entry (-16, -7)
    rw [show weight ((-16, -7) : Point) = -23 by decide]
    exact he
  have hh := hs.rotate .east
  change StandardHighwayFrom
    (rotateState .east (rotateState (inverseRotation .east) (singleBlack (1, 0)))) 2905 (-2, 2) at hh
  rw [inverse_rotateState] at hh
  exact hh

end LangtonsAnt
