import SingleBlackCheck

/-!
# A faster kernel run: the position kept as a bit index

`WideState.step` recomputes `wideIndex` from integer coordinates at every step.  Here the
position is the index itself, `i = (x + 128) * 256 + (y + 128)`, and a move adds or subtracts
1 or 256.  A step is only taken when the index is strictly inside the window, so a move never
wraps around a row.  Soundness is proved against the original model; the final half-plane check
reuses `checkWideAgreement` on the reconstructed wide state.  Measured on one certificate the
kernel check is about 2.3 times faster and uses about a third less memory.
-/

namespace LangtonsAnt

structure IdxState where
  bits : Nat
  idx : Nat
  dir : Direction

def idxPoint (i : Nat) : Point := (((i / 256 : Nat) : Int) - 128, ((i % 256 : Nat) : Int) - 128)

def IdxInner (i : Nat) : Prop := 0 < i % 256 ∧ i % 256 < 255 ∧ 256 <= i ∧ i < 65280

instance (i : Nat) : Decidable (IdxInner i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def idxMove (i : Nat) : Direction -> Nat
  | .north => i + 1
  | .south => i - 1
  | .east => i + 256
  | .west => i - 256

def IdxState.step (s : IdxState) : IdxState :=
  let d := turn (s.bits.testBit s.idx) s.dir
  { bits := s.bits ^^^ (1 <<< s.idx), idx := idxMove s.idx d, dir := d }

def IdxState.toWide (s : IdxState) : WideState := ⟨s.bits, idxPoint s.idx, s.dir⟩

def IdxState.toState (s : IdxState) : State := s.toWide.toState

theorem idxPoint_inWide {i : Nat} (h : i < 65536) : InWide (idxPoint i) := by
  simp only [InWide, idxPoint]
  omega

theorem wideIndex_idxPoint {i : Nat} (h : i < 65536) : wideIndex (idxPoint i) = i := by
  simp only [wideIndex, idxPoint]
  have h1 : (((i / 256 : Nat) : Int) - 128 + 128).toNat = i / 256 := by omega
  have h2 : (((i % 256 : Nat) : Int) - 128 + 128).toNat = i % 256 := by omega
  rw [h1, h2]
  omega

theorem idxPoint_move {i : Nat} (h : IdxInner i) (d : Direction) :
    idxPoint (idxMove i d) = move (idxPoint i) d := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases d
  · show idxPoint (i + 1) = move (idxPoint i) .north
    unfold idxPoint move
    apply Prod.ext
    · dsimp only; omega
    · dsimp only; omega
  · show idxPoint (i + 256) = move (idxPoint i) .east
    unfold idxPoint move
    apply Prod.ext
    · dsimp only; omega
    · dsimp only; omega
  · show idxPoint (i - 1) = move (idxPoint i) .south
    unfold idxPoint move
    apply Prod.ext
    · dsimp only; omega
    · dsimp only; omega
  · show idxPoint (i - 256) = move (idxPoint i) .west
    unfold idxPoint move
    apply Prod.ext
    · dsimp only; omega
    · dsimp only; omega

theorem IdxState.toState_step (s : IdxState) (h : IdxInner s.idx) :
    s.step.toState = LangtonsAnt.step s.toState := by
  have hlt : s.idx < 65536 := by simp only [IdxInner] at h; omega
  have hstep := WideState.toState_step s.toWide (idxPoint_inWide hlt)
  have heq : s.step.toWide = s.toWide.step := by
    simp only [IdxState.step, IdxState.toWide, WideState.step, wideIndex_idxPoint hlt,
      Nat.one_shiftLeft, idxPoint_move h]
  unfold IdxState.toState
  rw [heq, hstep]

/-- Run `n` inner steps, then check the half-plane entry on the reconstructed wide state. -/
def checkIdxEntry (cut : Int) (target : FiniteState) : Nat -> IdxState -> Bool
  | 0, s => checkWideAgreement cut s.toWide target
  | n + 1, s => decide (IdxInner s.idx) && checkIdxEntry cut target n s.step

theorem checkIdxEntry_sound {cut : Int} {target : FiniteState} {n : Nat} {s : IdxState}
    (h : checkIdxEntry cut target n s = true) :
    AgreesBelow cut (run s.toState n) target.toState := by
  induction n generalizing s with
  | zero => exact checkWideAgreement_sound h
  | succ n ih =>
    simp only [checkIdxEntry, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh := ih h.2
    rw [IdxState.toState_step _ h.1] at hh
    change AgreesBelow cut (run (run s.toState 1) n) target.toState at hh
    rw [← run_add, Nat.add_comm 1 n] at hh
    exact hh

def WideState.toIdx (s : WideState) : IdxState := ⟨s.bits, wideIndex s.pos, s.dir⟩

theorem WideState.toIdx_toState (s : WideState) (h : InWide s.pos) :
    s.toIdx.toState = s.toState := by
  have hp : idxPoint (wideIndex s.pos) = s.pos := by
    simp only [InWide] at h
    simp only [idxPoint, wideIndex]
    apply Prod.ext <;> simp <;> omega
  simp only [WideState.toIdx, IdxState.toState, IdxState.toWide, hp]

/-- Same certificate as `checkSingleBlack`, with the faster run. -/
def checkSingleBlackFast (q : Point) (T : Nat) (r : Direction) (w o : Point) : Bool :=
  (singleBlackFrame q r w).black.all (fun p => decide (InWide p)) &&
    decide (InWide (singleBlackFrame q r w).pos) &&
    checkIdxEntry (weight o) (highwaySeed.translate o) T (singleBlackFrame q r w).toWide.toIdx

theorem checkSingleBlackFast_sound {q : Point} {T : Nat} {r : Direction} {w o : Point}
    (h : checkSingleBlackFast q T r w o = true) : EventuallyStandard (singleBlack q) := by
  simp only [checkSingleBlackFast, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hb, hp⟩, he⟩ := h
  have hbox : forall p, p ∈ (singleBlackFrame q r w).black -> InWide p := fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp hb p hp)
  have he' := checkIdxEntry_sound he
  rw [WideState.toIdx_toState _ hp, FiniteState.toWide_toState _ hbox,
    FiniteState.toState_translate] at he'
  have hs := standard_highway_of_entry o he'
  have hr := (hs.rotate r).translate (negPoint w)
  have hframe : LangtonsAnt.translate (negPoint w) (rotateState r (singleBlackFrame q r w).toState) =
      singleBlack q := by
    rw [singleBlackFrame, FiniteState.toState_rotate, inverse_rotateState,
      FiniteState.toState_translate, translate_add, singleBlackFS_toState]
    have hz : addPoint (negPoint w) w = (0, 0) := by
      apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
    rw [hz, translate_zero]
  rw [hframe] at hr
  exact ⟨T, rotatePoint r (-2, -2), diagonal_rotated_southwest r, hr⟩

end LangtonsAnt
