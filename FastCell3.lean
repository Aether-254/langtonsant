import FastCell2

/-!
# `FastCell` without `let` in the step function

Diagnosis (2026-11-21): `IdxState.step` and `IdxState.step2` bind the new heading with
`let d := turn (...) s.dir` and use `d` in two fields.  Combined with the per-step guard
`decide (IdxInner s.idx)`, which projects the index of the previous step, the kernel's run time on
some certificates grows roughly exponentially with the number of steps: on one certificate
(cell `(-8, 11)`) the bare loop took 3.3 s for 4000 steps, 96 s for 8000 and more than 600 s for
18991.  Writing `turn (...)` directly into both fields removes the blow-up (7.6 s for the full
18991 steps).  Removing the guard instead also removes it.  A plausible explanation is that each
projection re-instantiates the `let`, producing fresh copies the kernel cache does not identify;
this is not confirmed against the kernel source.

The step below is definitionally the same as `IdxState.step`, so every soundness result carries
over through `checkIdxEntry3_eq`.
-/

namespace LangtonsAnt

def IdxState.step3 (s : IdxState) : IdxState :=
  { bits := s.bits ^^^ (2 ^ s.idx),
    idx := idxMove s.idx (turn (s.bits.testBit s.idx) s.dir),
    dir := turn (s.bits.testBit s.idx) s.dir }

theorem IdxState.step3_eq (s : IdxState) : s.step3 = s.step := by
  simp only [IdxState.step3, IdxState.step, Nat.one_shiftLeft]

def checkIdxEntry3 (cut : Int) (target : FiniteState) : Nat -> IdxState -> Bool
  | 0, s => checkWideAgreement cut s.toWide target
  | n + 1, s => decide (IdxInner s.idx) && checkIdxEntry3 cut target n s.step3

theorem checkIdxEntry3_eq (cut : Int) (target : FiniteState) (n : Nat) (s : IdxState) :
    checkIdxEntry3 cut target n s = checkIdxEntry cut target n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [checkIdxEntry3, checkIdxEntry, IdxState.step3_eq, ih]

def checkSingleBlackFast3 (q : Point) (T : Nat) (r : Direction) (w o : Point) : Bool :=
  (singleBlackFrame q r w).black.all (fun p => decide (InWide p)) &&
    decide (InWide (singleBlackFrame q r w).pos) &&
    checkIdxEntry3 (weight o) (highwaySeed.translate o) T (singleBlackFrame q r w).toWide.toIdx

theorem checkSingleBlackFast3_sound {q : Point} {T : Nat} {r : Direction} {w o : Point}
    (h : checkSingleBlackFast3 q T r w o = true) : EventuallyStandard (singleBlack q) := by
  apply checkSingleBlackFast_sound (T := T) (r := r) (w := w) (o := o)
  simpa only [checkSingleBlackFast3, checkSingleBlackFast, checkIdxEntry3_eq] using h

end LangtonsAnt
