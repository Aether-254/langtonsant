import MaturePhaseRecovery
import FirstContactDecision

namespace LangtonsAnt

-- Duplicate entries represent one black cell, and an out-of-box cell cannot certify recovery.
example : packedBoard (packCells [(0, 0), (0, 0)]) (0, 0) = true := by decide +kernel
example : checkPackedBounded 0 1 ⟨0, (64, 0), .north⟩ = false := by decide +kernel
example : checkRecovery 0 0 (1, 1) = false := by decide +kernel

example (k : Nat) : StandardHighwayFrom
    (flipCell (run highwaySeed.toState (104 * k + 1253))
      (run highwaySeed.toState (104 * k + 1253)).pos) 6645 (-2, -2) :=
  mature_phase_five_certificate.after_blocks (AgreesBelow.refl _ _) k

example (k : Nat) : StandardHighwayFrom
    (flipCell (run highwaySeed.toState (104 * k + 66))
      (run highwaySeed.toState (104 * k + 66)).pos) 174 (-2, -2) :=
  phase_sixty_six_certificate.after_blocks (AgreesBelow.refl _ _) k

example (k : Nat) : StandardHighwayFrom
    (flipCell (run highwaySeed.toState (104 * k + 94))
      (run highwaySeed.toState (104 * k + 94)).pos) 238 (-2, -2) :=
  phase_ninety_four_certificate.after_blocks (AgreesBelow.refl _ _) k

example (k : Nat) : StandardHighwayFrom
    (flipCell (run highwaySeed.toState (104 * k + 95))
      (run highwaySeed.toState (104 * k + 95)).pos) 337 (-2, -2) :=
  phase_ninety_five_certificate.after_blocks (AgreesBelow.refl _ _) k

example (k : Nat) : decideBlankContact [phaseFiveObstacle k] = some (phaseFiveContactTime k) := by
  apply (decideBlankContact_some_iff _ _).mpr
  have hv := phaseFiveObstacle_first_visit k
  refine ⟨by simp [cellsMask, hv.1], ?_⟩
  intro j hj
  simp [cellsMask, hv.2 j hj]

example (k : Nat) : StandardHighwayFrom (singleBlack (phaseFiveObstacle k))
    (19978 + 104 * k) (-2, -2) := phaseFiveObstacle_standard k

end LangtonsAnt
