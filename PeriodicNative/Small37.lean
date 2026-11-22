import PeriodicNative.Small35
import PeriodicNative.All36

/-! Extension to period 37: even period 36 by `native_decide`, blocks computed on Kaggle
(same trust base as `Small35`). -/

namespace LangtonsAnt

theorem no_consistent_word_native37 (P : Nat) (h1 : 0 < P) (h2 : P <= 37) (w : Nat -> Bool) :
    ¬ ConsistentWord P w := by
  by_cases hs : P <= 35
  · exact no_consistent_word_native35 P h1 hs w
  intro h
  have he := h.even
  have hcases : P = 36 := by omega
  subst hcases
  exact checkNoWords_sound checkNoWords_native_36 w h

theorem no_periodic_tail_native37 {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 37) : ¬ HighwayFrom s T P v := by
  intro h
  exact no_consistent_word_native37 P h1 h2 _ (periodic_tail_consistent_at_start hs h1 h)

end LangtonsAnt
