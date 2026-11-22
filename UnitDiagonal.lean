import UnitDiagonalInner

/-!
# Unit-diagonal full-drift exclusion (unconditional headline theorems)

Closes L30–L32 of the unit-diagonal exclusion blueprint by discharging `CoreUnitSE` via
`UnitDiagonalInner.third_inner_impossible` and instantiating the rotation/shift reduction
shell of `UnitDiagonalReduction`.

Every theorem below is checked purely by the Lean kernel (only standard axioms
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `axiom`, no `native_decide`).
-/
namespace UnitDiagonal
open LangtonsAnt

/-- L30: no consistent turn word has full one-period displacement `(1, -1)`. -/
theorem coreUnitSE : CoreUnitSE :=
  fun _ _ h hd => third_inner_impossible h hd

/-- Unconditional orbit-level unit-diagonal exclusion: no finite-support orbit with a
positive periodic tail has a full one-period displacement in `{(±1, ±1)}`. -/
theorem no_unit_diagonal_periodic_tail' {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (hv : UnitDiagonalDrift v) :
    ¬ HighwayFrom s T P v :=
  no_unit_diagonal_periodic_tail coreUnitSE hs hP hv

/-- Unconditional word-level unit-diagonal exclusion: no consistent turn word has a
full one-period displacement in `{(±1, ±1)}`. -/
theorem consistentWord_not_unitDiagonal' {P} {w} (h : ConsistentWord P w) :
    ¬ UnitDiagonalDrift (wordDrift P w) :=
  consistentWord_not_unitDiagonal coreUnitSE h

end UnitDiagonal
