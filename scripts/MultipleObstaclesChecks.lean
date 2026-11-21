import MultipleObstacles

namespace LangtonsAnt

example : chainCells 3 = [(-4, -4), (-12, -12), (-20, -20)] := by decide +kernel

example (p : Point) : (multipleObstacles 0).board p = false := by
  simp [multipleObstacles, initialChainMask, chainMask, chainCells, perturb, blank]

example : (multipleObstacles 3).board (-68, -42) = true := by decide +kernel
example : (multipleObstacles 3).board (-76, -50) = true := by decide +kernel
example : (multipleObstacles 3).board (-84, -58) = true := by decide +kernel
example : (multipleObstacles 3).board (-92, -66) = false := by decide +kernel

-- The final theorem quantifies over all obstacle counts without bounding them in the checker.
example (n : Nat) : StandardHighwayFrom (multipleObstacles n) (12496 + 548 * n) (-2, -2) :=
  multipleObstacles_standard n

example (n i : Nat) (hi : i < n) :
    (run (multipleObstacles n) (12604 + 548 * i)).pos =
      (-68 - 8 * (i : Int), -42 - 8 * (i : Int)) := multipleObstacles_visits n i hi

example (n i j : Nat) (hi : i < n) (hj : j < 12604 + 548 * i) :
    (run (multipleObstacles n) j).pos ≠ (-68 - 8 * (i : Int), -42 - 8 * (i : Int)) :=
  multipleObstacles_first_visits n i hi j hj

-- Existing color outside the certified half-plane is retained by every chain step.
example (n : Nat) (s : State) (h : AgreesBelow 0 s (perturb (chainMask n) highwaySeed.toState)) :
    StandardHighwayFrom s (548 * n) (-2, -2) := chain_standard n h

end LangtonsAnt
