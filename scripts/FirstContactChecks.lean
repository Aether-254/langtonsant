import FirstContactDecision
import CollisionRecovery

namespace LangtonsAnt

-- The search interval is [0, fuel), and the returned contact is the earliest one.
example : searchContact [(1, 0)] 1 finiteBlank = none := by decide +kernel
example : searchContact [(1, 0)] 2 finiteBlank = some 1 := by decide +kernel
example : decideBlankContact [(0, 0)] = some 0 := by decide +kernel
example : decideBlankContact [(1, 0)] = some 1 := by decide +kernel
example : decideBlankContact [(0, -1)] = some 3 := by decide +kernel
example : decideBlankContact [(0, -1), (1, 0), (1, 0)] = some 1 := by decide +kernel

-- Negative coordinates lengthen the bound even for a single-cell support.
example : contactBound [(0, 0)] = 12184 := by decide +kernel
example : contactBound [(-3, -4)] = 12912 := by decide +kernel

example : FirstContact (cellsMask [(1, 0)]) blank 1 :=
  decideBlankContact_some_first (by decide +kernel)

example : run (perturb (cellsMask [(1, 0)]) blank) 1 =
    perturb (cellsMask [(1, 0)]) (run blank 1) :=
  firstContact_state (decideBlankContact_some_first (by decide +kernel))

-- This is an infinite non-contact fact, not a finite simulation observation.
example : decideBlankContact [(100, 100)] = none := by
  apply (decideBlankContact_none_iff _).mpr
  intro n
  have hb := blank_all_bounded n
  have hn : (run blank n).pos ≠ (100, 100) := by
    intro he
    rw [he] at hb
    simp [weight] at hb
  simp [cellsMask, hn]

example : StandardHighwayFrom (singleBlack (0, 0)) 12081 (2, -2) :=
  singleBlack_origin_standard

example : StandardHighwayFrom (singleBlack (1, 0)) 2905 (-2, 2) :=
  singleBlack_east_standard

example : StandardHighwayFrom (flipCell highwaySeed.toState highwaySeed.toState.pos)
    276 (-2, -2) := standard_seed_flip_recovers

def seedWithDistantHistory : FiniteState :=
  { highwaySeed with black := (100, 100) :: (4, 4) :: highwaySeed.black }

example : StandardHighwayFrom
    (flipCell seedWithDistantHistory.toState seedWithDistantHistory.toState.pos) 276 (-2, -2) := by
  apply standard_seed_flip_recovers_of_matches
  exact checkAgreement_sound (by decide +kernel)

-- Being behind the original highway boundary alone does not certify flip recovery.
example : checkAgreement 7
    { highwaySeed with black := (4, 3) :: highwaySeed.black } highwaySeed = false := by
  decide +kernel

end LangtonsAnt
