import HighwayRecovery

namespace LangtonsAnt

def phaseFourSeed : FiniteState := highwaySeed.run 4

def flippedPhaseFourSeed : FiniteState :=
  { phaseFourSeed with black := toggleCells phaseFourSeed.black phaseFourSeed.pos }

theorem phaseFourSeed_toState : phaseFourSeed.toState = run highwaySeed.toState 4 :=
  highwaySeed.toState_run 4

theorem flippedPhaseFourSeed_toState :
    flippedPhaseFourSeed.toState = flipCell phaseFourSeed.toState phaseFourSeed.toState.pos :=
  phaseFourSeed.toState_flip phaseFourSeed.pos

theorem phaseFourSeed_pos : phaseFourSeed.toState.pos = (-2, -2) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem phaseFour_recovery_entry_check :
    checkAgreement (-12) (flippedPhaseFourSeed.run 440)
      (highwaySeed.translate (-6, -6)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem phaseFour_recovery_bound_check : checkBounded 0 440 flippedPhaseFourSeed = true := by
  decide +kernel

theorem phaseFour_recovery_entry :
    AgreesBelow (-12) (run flippedPhaseFourSeed.toState 440)
      (translate (-6, -6) highwaySeed.toState) := by
  have h := checkAgreement_sound phaseFour_recovery_entry_check
  simpa only [FiniteState.toState_run, FiniteState.toState_translate] using h

theorem phaseFour_recovery_standard :
    StandardHighwayFrom flippedPhaseFourSeed.toState 440 (-2, -2) := by
  apply standard_highway_of_entry (-6, -6)
  rw [show weight ((-6, -6) : Point) = -12 by decide]
  exact phaseFour_recovery_entry

theorem phaseFour_recovery_bounded (n : Nat) :
    weight (run flippedPhaseFourSeed.toState n).pos <= 0 := by
  by_cases hn : n < 440
  · exact checkBounded_sound phaseFour_recovery_bound_check n hn
  · have hc := highwaySeed_certificate.translate (-6, -6)
    have he : AgreesBelow (0 + weight (-6, -6)) (run flippedPhaseFourSeed.toState 440)
        (translate (-6, -6) highwaySeed.toState) := phaseFour_recovery_entry
    have hm := hc.matches_forever he (n - 440)
    have hb := hc.all_bounded (n - 440)
    rw [← hm.pos, ← run_add] at hb
    have heq : 440 + (n - 440) = n := by omega
    rw [heq] at hb
    change weight (run flippedPhaseFourSeed.toState n).pos <= -12 at hb
    omega

theorem phaseFour_flip_recovers_translated {s : State} (v : Point)
    (h : AgreesBelow (weight v) s (translate v phaseFourSeed.toState)) :
    StandardHighwayFrom (flipCell s s.pos) 440 (-2, -2) := by
  have hr := phaseFour_recovery_standard.translate v
  apply hr.of_agreesBelow
  · rw [flippedPhaseFourSeed_toState, ← flipCell_translate, h.pos]
    change AgreesBelow (weight v)
      (flipCell s (addPoint v phaseFourSeed.toState.pos))
      (flipCell (translate v phaseFourSeed.toState) (addPoint v phaseFourSeed.toState.pos))
    rw [flipCell_eq_perturb, flipCell_eq_perturb]
    exact h.perturb _
  · intro n
    rw [translate_run]
    change weight (addPoint v (run flippedPhaseFourSeed.toState n).pos) <= _
    rw [weight_addPoint]
    have hb := phaseFour_recovery_bounded n
    omega

theorem highway_flip_recovers_at_phase_four {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    StandardHighwayFrom (flipCell (run s (104 * k + 4)) (run s (104 * k + 4)).pos)
      440 (-2, -2) := by
  let v := offset (-2, -2) k
  have hm := highwaySeed_certificate.matches_forever h (104 * k + 4)
  have hp := highwaySeed_certificate.block_prefix k 4 (by decide)
  have hv : weight v <= 0 := offset_nonpos (by decide) k
  have he : AgreesBelow (weight v) (run s (104 * k + 4)) (translate v phaseFourSeed.toState) := by
    rw [phaseFourSeed_toState]
    exact (hm.weaken hv).trans (by simpa only [Int.zero_add] using hp)
  exact phaseFour_flip_recovers_translated v he

theorem EntryAt.flip_recovers_at_phase_four {s : State} {T : Nat} {r : Direction} {origin : Point}
    (h : EntryAt s T r origin) (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (T + (104 * k + 4))) (run s (T + (104 * k + 4))).pos)
      440 (rotatePoint r (-2, -2)) := by
  have hh := highway_flip_recovers_at_phase_four h k
  have hp := (hh.rotate r).translate origin
  change StandardHighwayFrom
    (pose r origin (flipCell (run (normalize r origin (run s T)) (104 * k + 4))
      (run (normalize r origin (run s T)) (104 * k + 4)).pos)) 440 _ at hp
  rw [← flipCell_pose, ← pose_run, pose_normalize, ← run_add] at hp
  exact hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The standard cycle has no diagonal cell at or southwest of (-4,-4). -/
theorem standard_cycle_diagonal_check :
    forall j : Fin 104, let p := (highwaySeed.run j.val).pos
      p.1 = p.2 -> -4 < p.1 := by
  decide +kernel

theorem phaseFour_first_in_cycle_check :
    forall j : Fin 4, (highwaySeed.run j.val).pos ≠ (-2, -2) := by decide +kernel

theorem phaseFour_first_visit (k : Nat) :
    (run highwaySeed.toState (104 * k + 4)).pos = addPoint (offset (-2, -2) k) (-2, -2) ∧
    forall n, n < 104 * k + 4 ->
      (run highwaySeed.toState n).pos ≠ addPoint (offset (-2, -2) k) (-2, -2) := by
  constructor
  · have hp := (highwaySeed_certificate.block_prefix k 4 (by decide)).pos
    change _ = addPoint (offset (-2, -2) k) (run highwaySeed.toState 4).pos at hp
    rw [← phaseFourSeed_toState, phaseFourSeed_pos] at hp
    exact hp
  · intro n hn he
    let q := n / 104
    let j := n % 104
    have hj : j < 104 := Nat.mod_lt _ (by decide)
    have hdecomp : 104 * q + j = n := Nat.div_add_mod n 104
    have hp := (highwaySeed_certificate.block_prefix q j (by omega)).pos
    rw [hdecomp] at hp
    rw [hp] at he
    change addPoint (offset (-2, -2) q) (run highwaySeed.toState j).pos = _ at he
    have hq : q <= k := by omega
    by_cases hsame : q = k
    · have heq : (run highwaySeed.toState j).pos = (-2, -2) := by
        rw [hsame] at he
        apply Prod.ext <;> simp only [addPoint, Prod.mk.injEq] at he ⊢ <;> omega
      have hj4 : j < 4 := by omega
      have hc := phaseFour_first_in_cycle_check ⟨j, hj4⟩
      have hr : (highwaySeed.run j).pos = (run highwaySeed.toState j).pos :=
        congrArg State.pos (highwaySeed.toState_run j)
      exact hc (hr.trans heq)
    · have hlt : q < k := by omega
      have hc := standard_cycle_diagonal_check ⟨j, hj⟩
      change (highwaySeed.run j).pos.1 = (highwaySeed.run j).pos.2 ->
        -4 < (highwaySeed.run j).pos.1 at hc
      have hr : (highwaySeed.run j).pos = (run highwaySeed.toState j).pos :=
        congrArg State.pos (highwaySeed.toState_run j)
      rw [hr] at hc
      rw [southwest_offset, southwest_offset] at he
      simp only [addPoint, Prod.mk.injEq] at he
      have hequal : (run highwaySeed.toState j).pos.1 = (run highwaySeed.toState j).pos.2 := by omega
      have hb := hc hequal
      omega

end LangtonsAnt
