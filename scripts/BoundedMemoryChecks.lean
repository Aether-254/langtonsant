import Ballistic

namespace LangtonsAnt

-- The zero-width window still has a finite universe of four directions.
example : memoryKeys 0 = [(.north, []), (.east, []), (.south, []), (.west, [])] := by
  decide +kernel

-- A fresh initial black cell is excluded by the strong memory definition.
example (s : State) (hblack : s.board s.pos = true) (W : Nat) :
    ¬BoundedMemoryFrom s 0 W := by
  intro h
  rcases h 0 (by omega) with ⟨j, hj, _⟩ | ⟨_, hc⟩
  · omega
  · simp only [run_zero, hblack] at hc
    contradiction

example (s : State) (T : Nat) (a b q C : Int) : ¬BallisticFrom s T a b 0 q C := by
  intro h
  have := h.rate_pos
  omega

example (s : State) (T : Nat) (a b p C : Int) : ¬BallisticFrom s T a b p 0 C := by
  intro h
  have := h.denominator_pos
  omega

example (s : State) (T : Nat) (a b p q : Int) : ¬BallisticFrom s T a b p q (-1) := by
  intro h
  have := h.backtrack_nonneg
  omega

-- Empty finite sets and the original start-time constraint are both supported.
example {s : State} {T : Nat} {a b p q C : Int} (h : BallisticFrom s T a b p q C) :
    exists U, T <= U ∧ forall n, U <= n -> (run s n).pos ∉ ([] : List Point) :=
  h.avoids_finite []

-- L1 accepts arbitrary boards; L3 is the step that requires finite support.
example {s : State} {T W : Nat} (h : BoundedMemoryFrom s T W) :
    exists U P v, T <= U ∧ 0 < P ∧ v ≠ (0, 0) ∧ HighwayFrom s U P v := by
  obtain ⟨U, P, v, hU, hP, hv, hh, _⟩ := h.highway
  exact ⟨U, P, v, hU, hP, hv, hh⟩

example : exists a b, BallisticFrom blank 12080 a b 4 104 108 :=
  blank_highway.ballisticFrom_of_diagonal (by simp [DiagonalDrift])

example {s : State} (h : HighwayFrom s 0 104 (0, 0)) : False :=
  h.drift_ne_zero (by decide +kernel) rfl

end LangtonsAnt
