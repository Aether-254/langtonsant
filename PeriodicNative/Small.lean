import PeriodicWordSmall
import PeriodicNative.All14
import PeriodicNative.All16
import PeriodicNative.All18
import PeriodicNative.All20
import PeriodicNative.All22
import PeriodicNative.All24
import PeriodicNative.All26
import PeriodicNative.All28
import PeriodicNative.All30
import PeriodicNative.All32

/-!
# No periodic tails with period at most 33

Even periods 2..12 come from the pure kernel checks of `PeriodicWordSmall`; even periods 14..32 from
the `native_decide` block scans in `PeriodicNative.All*`; odd periods are excluded structurally.
**Trust base**: the results below depend on `native_decide`, i.e. on the Lean compiler and the
compiled checker `fastCheck` (proved equal to `checkConsistentWord` by `fastCheck_eq`), in addition
to the kernel.  The pure-kernel statement `no_periodic_tail_small` (period <= 13) is unchanged.
-/

namespace LangtonsAnt

theorem no_consistent_word_native (P : Nat) (h1 : 0 < P) (h2 : P <= 33) (w : Nat -> Bool) :
    ¬ ConsistentWord P w := by
  by_cases hs : P <= 13
  · exact no_consistent_word_small P h1 hs w
  intro h
  have he := h.even
  have hcases : P = 14 ∨ P = 16 ∨ P = 18 ∨ P = 20 ∨ P = 22 ∨ P = 24 ∨ P = 26 ∨ P = 28 ∨ P = 30 ∨ P = 32 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkNoWords_sound checkNoWords_native_14 w h
  · exact checkNoWords_sound checkNoWords_native_16 w h
  · exact checkNoWords_sound checkNoWords_native_18 w h
  · exact checkNoWords_sound checkNoWords_native_20 w h
  · exact checkNoWords_sound checkNoWords_native_22 w h
  · exact checkNoWords_sound checkNoWords_native_24 w h
  · exact checkNoWords_sound checkNoWords_native_26 w h
  · exact checkNoWords_sound checkNoWords_native_28 w h
  · exact checkNoWords_sound checkNoWords_native_30 w h
  · exact checkNoWords_sound checkNoWords_native_32 w h

theorem no_periodic_tail_native {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (h1 : 0 < P) (h2 : P <= 33) : ¬ HighwayFrom s T P v := by
  intro h
  exact no_consistent_word_native P h1 h2 _ (periodic_tail_consistent_at_start hs h1 h)

end LangtonsAnt
