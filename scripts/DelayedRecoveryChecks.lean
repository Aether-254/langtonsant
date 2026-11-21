import DelayedRecovery
import FirstContactDecision

namespace LangtonsAnt

example : delayedObstacle 0 = (-66, -40) := by decide +kernel
example : delayedObstacle 1 = (-68, -42) := by decide +kernel
example : delayedContactTime 0 = 12500 := by decide +kernel
example : delayedContactTime 1 = 12604 := by decide +kernel

-- The independently proved first-visit geometry determines the total classifier's output.
example (k : Nat) : decideBlankContact [delayedObstacle k] = some (delayedContactTime k) := by
  apply (decideBlankContact_some_iff _ _).mpr
  have hv := delayedObstacle_first_visit k
  refine ⟨by simp [cellsMask, hv.1], ?_⟩
  intro n hn
  simp [cellsMask, hv.2 n hn]

example (k : Nat) : StandardHighwayFrom (singleBlack (delayedObstacle k))
    (12940 + 104 * k) (-2, -2) := delayedObstacle_standard k

-- A permanent highway cannot start 104 or more steps before the proved collision.
example (k T : Nat) (hT : T <= 12396 + 104 * k) :
    forall v, ¬HighwayFrom (singleBlack (delayedObstacle k)) T 104 v := by
  have hv := delayedObstacle_first_visit k
  apply singleBlack_no_highway_before_late_contact hv.1 hv.2
  · unfold delayedContactTime
    omega
  · unfold delayedContactTime
    omega

example (N : Nat) : exists p : Point, EventuallyStandard (singleBlack p) ∧
    forall T, T <= N -> forall v, ¬HighwayFrom (singleBlack p) T 104 v :=
  one_black_unbounded_delay_with_recovery N

-- Recovery after any certified entry is equivariant under direction and origin.
example (s : State) (T : Nat) (r : Direction) (origin : Point)
    (h : EntryAt s T r origin) (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (T + (104 * k + 4))) (run s (T + (104 * k + 4))).pos)
      440 (rotatePoint r (-2, -2)) := h.flip_recovers_at_phase_four k

end LangtonsAnt
