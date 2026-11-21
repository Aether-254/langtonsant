import InfiniteHighwayPeriod
import InfiniteChainLimit

namespace LangtonsAnt

-- The infinite mask is a one-sided ray, with exact spacing and no off-diagonal cells.
example : infiniteChainMask (-4, -4) = true := by decide +kernel
example : infiniteChainMask (-12, -12) = true := by decide +kernel
example : infiniteChainMask (4, 4) = false := by decide +kernel
example : infiniteChainMask (-8, -8) = false := by decide +kernel
example : infiniteChainMask (-12, -11) = false := by decide +kernel

example : infiniteObstacles.board (-68, -42) = true := by decide +kernel
example : infiniteObstacles.board (-76, -50) = true := by decide +kernel
example : infiniteObstacles.board (-60, -34) = false := by decide +kernel

example : HighwayFrom infiniteObstacles 12496 548 (-8, -8) := infiniteObstacles_highway
example : ¬FiniteSupport infiniteObstacles.board := infiniteObstacles_not_finite
example : ¬EventuallyStandard infiniteObstacles := infiniteObstacles_not_eventuallyStandard

-- Exclude smaller periods at every possible later start, with arbitrary integer displacement.
example (T q : Nat) (hq : 0 < q) (hsmall : q < 548) (v : Point) :
    ¬HighwayFrom infiniteObstacles T q v := infiniteObstacles_no_short_tail T q hq hsmall v

-- Two concrete witnesses reject the candidate periods 137 and 274.
example : obstacleColor 137 ≠ obstacleColor 0 := by decide +kernel
example : obstacleColor 275 ≠ obstacleColor 1 := by decide +kernel

example (N n : Nat) (hn : N <= n) (j : Nat) (hj : j <= N) :
    (run (multipleObstacles n) j).pos = (run infiniteObstacles j).pos ∧
    (run (multipleObstacles n) j).dir = (run infiniteObstacles j).dir ∧
    readColor (multipleObstacles n) j = readColor infiniteObstacles j :=
  finiteChains_match_infinite_prefix N n hn j hj

end LangtonsAnt
