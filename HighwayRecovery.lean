import CollisionRecovery

namespace LangtonsAnt

theorem flipCell_translate (s : State) (p v : Point) :
    flipCell (translate v s) (addPoint v p) = translate v (flipCell s p) := by
  have hb : flip (fun q => s.board (subPoint q v)) (addPoint v p) =
      fun q => flip s.board p (subPoint q v) := by
    funext q
    have heq : q = addPoint v p ↔ subPoint q v = p := by
      constructor
      · intro h; rw [h, subPoint_addPoint]
      · intro h; rw [← h, addPoint_subPoint]
    simp [flip, heq]
  simp only [flipCell, translate, hb]

/-- Two complete periods retain the wake needed by the recovery excursion. -/
def twoPeriodSeed : FiniteState := highwaySeed.run 208

def flippedTwoPeriodSeed : FiniteState :=
  { twoPeriodSeed with black := toggleCells twoPeriodSeed.black twoPeriodSeed.pos }

theorem twoPeriodSeed_toState : twoPeriodSeed.toState = run highwaySeed.toState 208 :=
  highwaySeed.toState_run 208

set_option maxRecDepth 100000 in
theorem flippedTwoPeriodSeed_toState :
    flippedTwoPeriodSeed.toState = flipCell twoPeriodSeed.toState twoPeriodSeed.toState.pos :=
  twoPeriodSeed.toState_flip twoPeriodSeed.pos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem twoPeriod_recovery_entry_check :
    checkAgreement (-20) (flippedTwoPeriodSeed.run 592)
      (highwaySeed.translate (-10, -10)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem twoPeriod_recovery_bound_check : checkBounded (-2) 592 flippedTwoPeriodSeed = true := by
  decide +kernel

theorem twoPeriod_recovery_entry :
    AgreesBelow (-20) (run flippedTwoPeriodSeed.toState 592)
      (translate (-10, -10) highwaySeed.toState) := by
  have h := checkAgreement_sound twoPeriod_recovery_entry_check
  simpa only [FiniteState.toState_run, FiniteState.toState_translate] using h

theorem twoPeriod_recovery_standard :
    StandardHighwayFrom flippedTwoPeriodSeed.toState 592 (-2, -2) := by
  apply standard_highway_of_entry (-10, -10)
  rw [show weight ((-10, -10) : Point) = -20 by decide]
  exact twoPeriod_recovery_entry

theorem twoPeriod_recovery_bounded (n : Nat) :
    weight (run flippedTwoPeriodSeed.toState n).pos <= 0 := by
  by_cases hn : n < 592
  · have hb := checkBounded_sound twoPeriod_recovery_bound_check n hn
    omega
  · have hc := highwaySeed_certificate.translate (-10, -10)
    have he : AgreesBelow (0 + weight (-10, -10)) (run flippedTwoPeriodSeed.toState 592)
        (translate (-10, -10) highwaySeed.toState) := twoPeriod_recovery_entry
    have hm := hc.matches_forever he (n - 592)
    have hb := hc.all_bounded (n - 592)
    rw [← hm.pos, ← run_add] at hb
    have heq : 592 + (n - 592) = n := by omega
    rw [heq] at hb
    change weight (run flippedTwoPeriodSeed.toState n).pos <= -20 at hb
    omega

theorem twoPeriod_flip_recovers_of_matches {s : State}
    (h : AgreesBelow 0 s twoPeriodSeed.toState) :
    StandardHighwayFrom (flipCell s s.pos) 592 (-2, -2) := by
  apply twoPeriod_recovery_standard.of_agreesBelow (hb := twoPeriod_recovery_bounded)
  rw [flippedTwoPeriodSeed_toState, h.pos, flipCell_eq_perturb, flipCell_eq_perturb]
  exact h.perturb (fun q => decide (q = twoPeriodSeed.toState.pos))

theorem twoPeriod_flip_recovers_translated {s : State} (v : Point)
    (h : AgreesBelow (weight v) s (translate v twoPeriodSeed.toState)) :
    StandardHighwayFrom (flipCell s s.pos) 592 (-2, -2) := by
  have hr := (twoPeriod_recovery_standard.translate v)
  apply hr.of_agreesBelow
  · rw [flippedTwoPeriodSeed_toState, ← flipCell_translate, h.pos]
    change AgreesBelow (weight v)
      (flipCell s (addPoint v twoPeriodSeed.toState.pos))
      (flipCell (translate v twoPeriodSeed.toState) (addPoint v twoPeriodSeed.toState.pos))
    rw [flipCell_eq_perturb, flipCell_eq_perturb]
    exact h.perturb _
  · intro n
    rw [translate_run]
    change weight (addPoint v (run flippedTwoPeriodSeed.toState n).pos) <= _
    rw [weight_addPoint]
    have hb := twoPeriod_recovery_bounded n
    omega

/-- At every later period boundary, an arbitrary certified history has the same recovery. -/
theorem highway_flip_recovers_after_two_periods {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (104 * k + 208)) (run s (104 * k + 208)).pos) 592 (-2, -2) := by
  let v := offset (-2, -2) k
  have hblocks := highwaySeed_certificate.blocks k
  have hm := highwaySeed_certificate.matches_forever h (104 * k)
  have hv : weight v <= 0 := offset_nonpos (by decide) k
  have he : AgreesBelow (weight v) (run s (104 * k)) (translate v highwaySeed.toState) :=
    (hm.weaken hv).trans (by simpa only [Int.zero_add] using hblocks)
  have hg := he.run 208 (by
    intro j _
    rw [translate_run]
    change weight (addPoint v (run highwaySeed.toState j).pos) <= _
    rw [weight_addPoint]
    have hb := highwaySeed_certificate.all_bounded j
    omega)
  rw [← run_add, translate_run, ← twoPeriodSeed_toState] at hg
  exact twoPeriod_flip_recovers_translated v hg

theorem flipCell_rotate (s : State) (p : Point) (r : Direction) :
    flipCell (rotateState r s) (rotatePoint r p) = rotateState r (flipCell s p) := by
  have hb : flip (fun q => s.board (rotatePoint (inverseRotation r) q)) (rotatePoint r p) =
      fun q => flip s.board p (rotatePoint (inverseRotation r) q) := by
    funext q
    have heq : q = rotatePoint r p ↔ rotatePoint (inverseRotation r) q = p := by
      constructor
      · intro h; rw [h, rotatePoint_inverse]
      · intro h; rw [← h, inverse_rotatePoint]
    simp [flip, heq]
  simp only [flipCell, rotateState, hb]

theorem flipCell_pose (s : State) (r : Direction) (origin : Point) :
    flipCell (pose r origin s) (pose r origin s).pos = pose r origin (flipCell s s.pos) := by
  change flipCell (translate origin (rotateState r s))
    (addPoint origin (rotatePoint r s.pos)) = _
  rw [flipCell_translate, flipCell_rotate]
  rfl

/-- The entry may have any direction, location, and history outside its protected half-plane. -/
theorem EntryAt.flip_recovers_after_two_periods {s : State} {T : Nat} {r : Direction} {origin : Point}
    (h : EntryAt s T r origin) (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (T + (104 * k + 208))) (run s (T + (104 * k + 208))).pos)
      592 (rotatePoint r (-2, -2)) := by
  have hh := highway_flip_recovers_after_two_periods h k
  have hp := (hh.rotate r).translate origin
  change StandardHighwayFrom
    (pose r origin (flipCell (run (normalize r origin (run s T)) (104 * k + 208))
      (run (normalize r origin (run s T)) (104 * k + 208)).pos)) 592 _ at hp
  rw [← flipCell_pose, ← pose_run, pose_normalize, ← run_add] at hp
  exact hp

/-- Every finite state already known to enter a highway has infinitely many certified flip times. -/
theorem EventuallyStandard.late_flip_recovery {s : State} (hs : FiniteSupport s.board)
    (h : EventuallyStandard s) :
    exists T r, forall k : Nat,
      StandardHighwayFrom
        (flipCell (LangtonsAnt.run s (T + 104 * k)) (LangtonsAnt.run s (T + 104 * k)).pos)
        592 (rotatePoint r (-2, -2)) := by
  obtain ⟨T, r, origin, he⟩ := h.enters hs
  refine ⟨T + 208, r, ?_⟩
  intro k
  have hh := he.flip_recovers_after_two_periods k
  have heq : T + (104 * k + 208) = T + 208 + 104 * k := by omega
  simpa only [heq] using hh

end LangtonsAnt
