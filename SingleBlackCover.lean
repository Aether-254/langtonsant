import WidePacked
import DelayedRecovery

/-!
# Every cell the blank orbit visits before time 13952 lies in a given finite list

`checkBlankCover bits n s` walks `n` steps of a wide-window run and checks, at every step, that
the current cell is in the window and that its bit is set in `bits`.  With `bits` the encoding of
a cell list, soundness gives list membership of every visited position.
-/

namespace LangtonsAnt

def checkBlankCover (bits : Nat) : Nat -> WideState -> Bool
  | 0, _ => true
  | n + 1, s => decide (InWide s.pos) && bits.testBit (wideIndex s.pos) &&
      checkBlankCover bits n s.step

theorem checkBlankCover_sound {bits n : Nat} {s : WideState}
    (h : checkBlankCover bits n s = true) :
    forall j, j < n -> InWide (run s.toState j).pos ∧
      bits.testBit (wideIndex (run s.toState j).pos) = true := by
  induction n generalizing s with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkBlankCover, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    cases j with
    | zero => exact ⟨h.1.1, h.1.2⟩
    | succ j =>
      have hh := ih h.2 j (by omega)
      rw [WideState.toState_step _ h.1.1] at hh
      have hr : run (step s.toState) j = run s.toState (j + 1) := by
        change run (run s.toState 1) j = _
        rw [← run_add, Nat.add_comm 1 j]
      rw [hr] at hh
      exact hh

def wideBlank : WideState := ⟨0, (0, 0), .north⟩

theorem wideBlank_toState : wideBlank.toState = blank := by
  have hb : wideBoard 0 = fun _ => false := by
    funext p
    simp [wideBoard]
  unfold WideState.toState wideBlank blank
  rw [hb]

/-- Cover theorem for a cell list, from one kernel computation. -/
theorem blank_cover_of_check {cells : List Point} {n : Nat}
    (hbox : cells.all (fun p => decide (InWide p)) = true)
    (h : checkBlankCover (wideCells cells) n wideBlank = true) :
    forall j, j < n -> (run blank j).pos ∈ cells := by
  intro j hj
  have hh := checkBlankCover_sound h j hj
  rw [wideBlank_toState] at hh
  have hbox' : forall p, p ∈ cells -> InWide p := fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp hbox p hp)
  have hb := congrFun (wideBoard_wideCells cells hbox') (run blank j).pos
  simp only [wideBoard, hh.1, ite_true, hh.2] at hb
  exact of_decide_eq_true hb.symm

end LangtonsAnt
