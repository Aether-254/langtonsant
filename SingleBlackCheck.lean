import WidePacked
import DelayedRecovery

/-!
# A kernel-checkable entry certificate for one single-black initial state

`checkSingleBlack q T r w o` runs the state "blank board, one black cell `q`, ant at the origin
facing north" in the frame `rotate (inverse r) ∘ translate w`, for `T` steps inside the wide
window, and checks that the result agrees with the standard seed translated to `o` on the whole
half-plane `x + y <= weight o`.  Soundness turns this into `EventuallyStandard (singleBlack q)`.
The parameters come from an untrusted search script; only the kernel check is relied on.
-/

namespace LangtonsAnt

def singleBlackFS (q : Point) : FiniteState := ⟨[q], (0, 0), .north⟩

theorem singleBlackFS_toState (q : Point) : (singleBlackFS q).toState = singleBlack q := by
  simp [singleBlackFS, FiniteState.toState, singleBlack]

def singleBlackFrame (q : Point) (r : Direction) (w : Point) : FiniteState :=
  ((singleBlackFS q).translate w).rotate (inverseRotation r)

def checkSingleBlack (q : Point) (T : Nat) (r : Direction) (w o : Point) : Bool :=
  (singleBlackFrame q r w).black.all (fun p => decide (InWide p)) &&
    checkWideEntry (weight o) (highwaySeed.translate o) T (singleBlackFrame q r w).toWide

theorem checkSingleBlack_sound {q : Point} {T : Nat} {r : Direction} {w o : Point}
    (h : checkSingleBlack q T r w o = true) : EventuallyStandard (singleBlack q) := by
  simp only [checkSingleBlack, Bool.and_eq_true] at h
  have hbox : forall p, p ∈ (singleBlackFrame q r w).black -> InWide p := fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp h.1 p hp)
  have he := checkWideEntry_sound h.2
  rw [FiniteState.toWide_toState _ hbox, FiniteState.toState_translate] at he
  have hs := standard_highway_of_entry o he
  have hr := (hs.rotate r).translate (negPoint w)
  have hframe : translate (negPoint w) (rotateState r (singleBlackFrame q r w).toState) =
      singleBlack q := by
    rw [singleBlackFrame, FiniteState.toState_rotate, inverse_rotateState,
      FiniteState.toState_translate, translate_add, singleBlackFS_toState]
    have hz : addPoint (negPoint w) w = (0, 0) := by
      apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
    rw [hz, translate_zero]
  rw [hframe] at hr
  exact ⟨T, rotatePoint r (-2, -2), diagonal_rotated_southwest r, hr⟩

end LangtonsAnt
