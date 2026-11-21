import FastCell

/-!
# `FastCell` with the flip mask computed as a power

`IdxState.step` flips with `1 <<< idx`.  On some certificates the kernel evaluates this mask
far more slowly than `2 ^ idx` (measured: one 25521-step certificate took 270 s with the shift
and 29 s with the old point-based step, which uses a power).  This file adds a second step
function with `2 ^ idx`; the original definitions are left unchanged because certificates have
already been checked against them.
-/

namespace LangtonsAnt

def IdxState.step2 (s : IdxState) : IdxState :=
  let d := turn (s.bits.testBit s.idx) s.dir
  { bits := s.bits ^^^ (2 ^ s.idx), idx := idxMove s.idx d, dir := d }

theorem IdxState.step2_eq (s : IdxState) : s.step2 = s.step := by
  simp only [IdxState.step2, IdxState.step, Nat.one_shiftLeft]

def checkIdxEntry2 (cut : Int) (target : FiniteState) : Nat -> IdxState -> Bool
  | 0, s => checkWideAgreement cut s.toWide target
  | n + 1, s => decide (IdxInner s.idx) && checkIdxEntry2 cut target n s.step2

theorem checkIdxEntry2_eq (cut : Int) (target : FiniteState) (n : Nat) (s : IdxState) :
    checkIdxEntry2 cut target n s = checkIdxEntry cut target n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [checkIdxEntry2, checkIdxEntry, IdxState.step2_eq, ih]

def checkSingleBlackFast2 (q : Point) (T : Nat) (r : Direction) (w o : Point) : Bool :=
  (singleBlackFrame q r w).black.all (fun p => decide (InWide p)) &&
    decide (InWide (singleBlackFrame q r w).pos) &&
    checkIdxEntry2 (weight o) (highwaySeed.translate o) T (singleBlackFrame q r w).toWide.toIdx

theorem checkSingleBlackFast2_sound {q : Point} {T : Nat} {r : Direction} {w o : Point}
    (h : checkSingleBlackFast2 q T r w o = true) : EventuallyStandard (singleBlack q) := by
  apply checkSingleBlackFast_sound (T := T) (r := r) (w := w) (o := o)
  simpa only [checkSingleBlackFast2, checkSingleBlackFast, checkIdxEntry2_eq] using h

end LangtonsAnt
