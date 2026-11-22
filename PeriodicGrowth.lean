import UnitDiagonal
import TwoCellAxial
import TwoCellDiagonal

/-!
# Growth lower bound `g ≥ 8` for periodic tails

Assembles blueprint item L26 (`research/growth-blueprint-2026-11-22.md`): by
`ConsistentWord.growth_four_drift_trichotomy`, growth `g = 4` forces a unit-diagonal,
two-cell axial or two-cell diagonal full drift, and each of the three is excluded
(`UnitDiagonal.consistentWord_not_unitDiagonal'`, `ConsistentWord.twoCellAxial_growth_ne_four`,
`ConsistentWord.twoCellDiagonal_growth_ne_four`). Together with `4 ∣ g` and `g ≥ 4` this gives
`g ≥ 8` (Ke, `periodic-growth-closure.md`, Theorem A; the mathematics is Jillhewar's and Ke's).

This is a necessary condition only; it does not settle `ConsistentWordsAreStandard`.
-/

namespace LangtonsAnt

/-- No consistent word has growth exactly `4`. -/
theorem ConsistentWord.growth_ne_four {P : Nat} {w : Nat → Bool} (h : ConsistentWord P w) :
    wordGrowth P w ≠ 4 := by
  intro hg
  rcases h.growth_four_drift_trichotomy hg with hu | ha | hdg
  · exact UnitDiagonal.consistentWord_not_unitDiagonal' h hu
  · exact h.twoCellAxial_growth_ne_four ha hg
  · exact h.twoCellDiagonal_growth_ne_four hdg hg

/-- **L26:** every consistent word has growth at least `8`. -/
theorem ConsistentWord.eight_le_growth {P : Nat} {w : Nat → Bool} (h : ConsistentWord P w) :
    8 ≤ wordGrowth P w := by
  have h4 := h.four_le_growth
  have hne := h.growth_ne_four
  obtain ⟨k, hk⟩ := h.four_dvd_growth
  omega

/-- **L26, orbit form:** every positive-period tail of a finite-support orbit has growth at
least `8` (net black-cell growth per period, `HighwayFrom.net_black_growth`). -/
theorem periodic_tail_eight_le_growth {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    8 ≤ wordGrowth P (fun i => readColor s (T + i)) :=
  (periodic_tail_consistent_at_start hs hP h).eight_le_growth

end LangtonsAnt
