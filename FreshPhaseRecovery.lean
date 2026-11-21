import MaturePhaseRecovery
import FreshPhases
import RotatedRecovery

/-!
# Recovery certificates for further first-visit phases

Candidates were found by `scripts/ExploreFreshPhaseRecovery.lean` (exploration only).
Each certificate below is re-verified by `checkRecovery` and the kernel; the exploration
output is not trusted.  These are same-direction recoveries; phases whose mature recovery
turns to another heading need a rotated certificate and are not covered here.
-/

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_thirty_seven_check : checkRecovery (104 * 10 + 37) 2533 (-35, -21) = true := by
  decide +kernel

theorem phase_thirty_seven_certificate : RecoveryCertificate (104 * 10 + 37) 2533 (-35, -21) :=
  checkRecovery_sound phase_thirty_seven_check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_forty_seven_check : checkRecovery (104 * 3 + 47) 8585 (-36, -20) = true := by
  decide +kernel

theorem phase_forty_seven_certificate : RecoveryCertificate (104 * 3 + 47) 8585 (-36, -20) :=
  checkRecovery_sound phase_forty_seven_check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_fifty_two_check : checkRecovery (104 * 5 + 52) 3688 (-26, -22) = true := by
  decide +kernel

theorem phase_fifty_two_certificate : RecoveryCertificate (104 * 5 + 52) 3688 (-26, -22) :=
  checkRecovery_sound phase_fifty_two_check

/-! Quarter-turn recoveries: the new highway heads northwest (`east`) or southeast (`west`). -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_nine_check : checkRotatedRecovery (104 * 7 + 9) 8662 .east (-38, 21) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_fifteen_check : checkRotatedRecovery (104 * 8 + 15) 5716 .east (-14, -1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_twenty_two_check : checkRotatedRecovery (104 * 8 + 22) 2131 .west (-9, -28) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_twenty_three_check : checkRotatedRecovery (104 * 3 + 23) 600 .west (-2, -17) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_twenty_four_check : checkRotatedRecovery (104 * 3 + 24) 643 .west (-2, -17) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_thirty_two_check : checkRotatedRecovery (104 * 13 + 32) 6707 .east (-20, 5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_thirty_three_check : checkRotatedRecovery (104 * 8 + 33) 7428 .east (-33, -2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_thirty_four_check : checkRotatedRecovery (104 * 1 + 34) 693 .west (0, -15) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_thirty_nine_check : checkRotatedRecovery (104 * 13 + 39) 7390 .east (-33, -10) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_forty_eight_check : checkRotatedRecovery (104 * 9 + 48) 16227 .east (-34, 3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_ninety_six_check : checkRotatedRecovery (104 * 6 + 96) 3673 .west (-9, -36) = true := by
  decide +kernel

/-! ## Uniform statement for the certified first-visit phases -/

theorem RecoveryCertificate.eventually_shift {f d H phi : Nat} {o : Point}
    (c : RecoveryCertificate f d o) (hf : f = 104 * H + phi) {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    EventuallyStandard
      (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos) := by
  have e : 104 * (k + H) + phi = 104 * k + f := by omega
  rw [e]
  exact ⟨d, (-2, -2), diagonal_rotated_southwest .north, c.after_blocks h k⟩

theorem RotatedRecoveryCertificate.eventually_shift {f d H phi : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) (hf : f = 104 * H + phi) {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    EventuallyStandard
      (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos) := by
  have e : 104 * (k + H) + phi = 104 * k + f := by omega
  rw [e]
  exact c.eventually h k

/-- First-visit phases with a kernel-checked recovery certificate (19 of the 22). -/
def certifiedFreshPhases : List Nat :=
  [4, 5, 9, 15, 22, 23, 24, 32, 33, 34, 37, 39, 47, 48, 52, 66, 94, 95, 96]

theorem certifiedFreshPhases_sub : certifiedFreshPhases.all (· ∈ freshPhases) = true := by decide

theorem uncertifiedFreshPhases :
    freshPhases.filter (· ∉ certifiedFreshPhases) = [6, 38, 49] := by decide

/-- For every certified first-visit phase there is a history length `H` such that, after any
history outside the protected half-plane and any number of further periods, flipping the
current cell at that phase leads to an eventually standard state. -/
theorem certified_fresh_phase_recovers (phi : Nat) (hphi : phi ∈ certifiedFreshPhases) :
    exists H : Nat, forall s : State, AgreesBelow 0 s highwaySeed.toState -> forall k : Nat,
      EventuallyStandard
        (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos) := by
  simp only [certifiedFreshPhases, List.mem_cons, List.not_mem_nil, or_false] at hphi
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, fun s h k => by
      rw [Nat.add_zero]
      exact ⟨440, (-2, -2), diagonal_rotated_southwest .north,
        highway_flip_recovers_at_phase_four h k⟩⟩
  · exact ⟨12, fun s h k => mature_phase_five_certificate.eventually_shift (by decide) h k⟩
  · exact ⟨7, fun s h k =>
      (checkRotatedRecovery_sound phase_nine_check).eventually_shift rfl h k⟩
  · exact ⟨8, fun s h k =>
      (checkRotatedRecovery_sound phase_fifteen_check).eventually_shift rfl h k⟩
  · exact ⟨8, fun s h k =>
      (checkRotatedRecovery_sound phase_twenty_two_check).eventually_shift rfl h k⟩
  · exact ⟨3, fun s h k =>
      (checkRotatedRecovery_sound phase_twenty_three_check).eventually_shift rfl h k⟩
  · exact ⟨3, fun s h k =>
      (checkRotatedRecovery_sound phase_twenty_four_check).eventually_shift rfl h k⟩
  · exact ⟨13, fun s h k =>
      (checkRotatedRecovery_sound phase_thirty_two_check).eventually_shift rfl h k⟩
  · exact ⟨8, fun s h k =>
      (checkRotatedRecovery_sound phase_thirty_three_check).eventually_shift rfl h k⟩
  · exact ⟨1, fun s h k =>
      (checkRotatedRecovery_sound phase_thirty_four_check).eventually_shift rfl h k⟩
  · exact ⟨10, fun s h k => phase_thirty_seven_certificate.eventually_shift rfl h k⟩
  · exact ⟨13, fun s h k =>
      (checkRotatedRecovery_sound phase_thirty_nine_check).eventually_shift rfl h k⟩
  · exact ⟨3, fun s h k => phase_forty_seven_certificate.eventually_shift rfl h k⟩
  · exact ⟨9, fun s h k =>
      (checkRotatedRecovery_sound phase_forty_eight_check).eventually_shift rfl h k⟩
  · exact ⟨5, fun s h k => phase_fifty_two_certificate.eventually_shift rfl h k⟩
  · exact ⟨0, fun s h k => phase_sixty_six_certificate.eventually_shift (by decide) h k⟩
  · exact ⟨0, fun s h k => phase_ninety_four_certificate.eventually_shift (by decide) h k⟩
  · exact ⟨0, fun s h k => phase_ninety_five_certificate.eventually_shift (by decide) h k⟩
  · exact ⟨6, fun s h k =>
      (checkRotatedRecovery_sound phase_ninety_six_check).eventually_shift rfl h k⟩

end LangtonsAnt
