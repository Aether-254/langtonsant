import PeriodicNative.Small
import PeriodicNative.All34

/-! Extension to period 35 (even period 34 by `native_decide`; same trust base as `Small`). -/

namespace LangtonsAnt

theorem no_consistent_word_native35 (P : Nat) (h1 : 0 < P) (h2 : P <= 35) (w : Nat -> Bool) :
    ¬ ConsistentWord P w := by
  by_cases hs : P <= 33
  · exact no_consistent_word_native P h1 hs w
  intro h
  have he := h.even
  have hcases : P = 34 := by omega
  subst hcases
  exact checkNoWords_sound checkNoWords_native_34 w h

theorem no_periodic_tail_native35 {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 35) : ¬ HighwayFrom s T P v := by
  intro h
  exact no_consistent_word_native35 P h1 h2 _ (periodic_tail_consistent_at_start hs h1 h)

end LangtonsAnt
