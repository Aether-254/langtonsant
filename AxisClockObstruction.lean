import FiniteAnt

namespace LangtonsAnt

namespace AxisClockObstruction

def eastSeed : FiniteState := ⟨[(1, -1), (2, -1)], (0, 0), .north⟩

def westSeed : FiniteState := ⟨[(0, 0), (-1, 0)], (0, 0), .north⟩

theorem east_four : eastSeed.run 4 = ⟨[(1, 0), (0, 0)], (2, 0), .north⟩ := by
  decide +kernel

theorem west_four : westSeed.run 4 = ⟨[(-2, -1), (-1, -1)], (-2, 0), .north⟩ := by
  decide +kernel

/-- A complete finite black-field sum, with an arbitrary head correction. -/
def clock (field : Point -> Int) (head : Point -> Direction -> Int) (s : FiniteState) : Int :=
  (s.black.map field).sum + head s.pos s.dir

def TwoPeriodic (field : Point -> Int) : Prop :=
  forall x y, field (x + 2, y) = field (x, y)

def HeadTwoPeriodic (head : Point -> Direction -> Int) : Prop :=
  forall x y d, head (x + 2, y) d = head (x, y) d

/-- The two genuine four-step paths have opposite clock increments.
They are different finite initial states, not a periodic ant orbit. -/
theorem increment_cancellation (field : Point -> Int) (head : Point -> Direction -> Int)
    (hf : TwoPeriodic field) (hh : HeadTwoPeriodic head) :
    clock field head (eastSeed.run 4) + clock field head (westSeed.run 4) =
      clock field head eastSeed + clock field head westSeed := by
  rw [east_four, west_four]
  have hf0 := hf 0 (-1)
  have hf1 := hf (-1) (-1)
  have hf2 := hf (-2) (-1)
  have hf3 := hf (-1) 0
  have hh0 := hh 0 0 .north
  have hh1 := hh (-2) 0 .north
  simp only [Int.reduceAdd] at hf0 hf1 hf2 hf3 hh0 hh1
  simp only [clock, eastSeed, westSeed, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem strict_four (f : FiniteState -> Int)
    (h : forall s : FiniteState, s.black.Nodup -> axisParity s.toState = 0 -> f s < f s.step)
    (s : FiniteState) (haxis : axisParity s.toState = 0)
    (h0 : s.black.Nodup) (h1 : (s.run 1).black.Nodup)
    (h2 : (s.run 2).black.Nodup) (h3 : (s.run 3).black.Nodup) :
    f s < f (s.run 4) := by
  have hp (n : Nat) : axisParity (s.run n).toState = 0 := by
    rw [FiniteState.toState_run, axisParity_run]
    exact haxis
  have a := h s h0 haxis
  have b := h (s.run 1) h1 (hp 1)
  have c := h (s.run 2) h2 (hp 2)
  have d := h (s.run 3) h3 (hp 3)
  change f s < f (s.run 1) at a
  change f (s.run 1) < f (s.run 2) at b
  change f (s.run 2) < f (s.run 3) at c
  change f (s.run 3) < f (s.run 4) at d
  omega

/-- No two-cell horizontally periodic additive integer clock is strictly increasing
on all finite-support states, even in a fixed checker/heading sector.
This does not rule out clocks restricted to periodic tails. -/
theorem no_universal_strict_clock (field : Point -> Int) (head : Point -> Direction -> Int)
    (hf : TwoPeriodic field) (hh : HeadTwoPeriodic head) :
    ¬ (forall s : FiniteState, s.black.Nodup -> axisParity s.toState = 0 ->
      clock field head s < clock field head s.step) := by
  intro h
  have he := strict_four (clock field head) h eastSeed
    (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hw := strict_four (clock field head) h westSeed
    (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hc := increment_cancellation field head hf hh
  omega

end AxisClockObstruction

end LangtonsAnt
