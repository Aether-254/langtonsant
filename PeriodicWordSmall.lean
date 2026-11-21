import PeriodicWord
import PeriodicWordCheck12

namespace LangtonsAnt

/-- Even lengths through 12 are kernel-enumerated; all odd lengths are excluded structurally. -/
theorem no_consistent_word_small (P : Nat) (h1 : 0 < P) (h2 : P <= 13) (w : Nat -> Bool) :
    ¬ ConsistentWord P w := by
  intro h
  have he := h.even
  have hcases : P = 2 ∨ P = 4 ∨ P = 6 ∨ P = 8 ∨ P = 10 ∨ P = 12 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkNoWords_sound checkNoWords_two w h
  · exact checkNoWords_sound checkNoWords_four w h
  · exact checkNoWords_sound checkNoWords_six w h
  · exact checkNoWords_sound checkNoWords_eight w h
  · exact checkNoWords_sound checkNoWords_ten w h
  · exact checkNoWords_sound checkNoWords_twelve w h

theorem no_periodic_tail_small {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 13) : ¬ HighwayFrom s T P v := by
  intro h
  exact no_consistent_word_small P h1 h2 _ (periodic_tail_consistent_at_start hs h1 h)

end LangtonsAnt
