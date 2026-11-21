import HighwayRecovery

namespace LangtonsAnt

def seedWithOutsideHistory : FiniteState :=
  { highwaySeed with black := (1, 0) :: (100, 100) :: highwaySeed.black }

-- The new result only needs the original boundary, including arbitrary adjacent history.
example : checkAgreement 0 seedWithOutsideHistory highwaySeed = true := by decide +kernel
example : checkAgreement 7 seedWithOutsideHistory highwaySeed = false := by decide +kernel

example (k : Nat) : StandardHighwayFrom
    (flipCell (run seedWithOutsideHistory.toState (104 * k + 208))
      (run seedWithOutsideHistory.toState (104 * k + 208)).pos) 592 (-2, -2) := by
  apply highway_flip_recovers_after_two_periods
  exact checkAgreement_sound (by decide +kernel)

-- A symbolic cycle count checks the infinite claim; no enumeration of k is used.
example (k : Nat) : StandardHighwayFrom
    (flipCell (run highwaySeed.toState (104 * k + 208))
      (run highwaySeed.toState (104 * k + 208)).pos) 592 (-2, -2) :=
  highway_flip_recovers_after_two_periods (AgreesBelow.refl _ _) k

example (k : Nat) : StandardHighwayFrom
    (flipCell (run blank (12080 + (104 * k + 208)))
      (run blank (12080 + (104 * k + 208))).pos) 592 (-2, -2) := by
  have he : EntryAt blank 12080 .north (-56, -30) := by
    have hb : AgreesBelow (weight (-56, -30)) (run blank 12080)
        (translate (-56, -30) highwaySeed.toState) := blank_entry
    have hh := hb.normalize_translate
    have hr (s : State) : rotateState .north s = s := by cases s; rfl
    simpa only [EntryAt, normalize, inverseRotation, hr] using hh
  exact he.flip_recovers_after_two_periods k

example (s : State) (hs : FiniteSupport s.board) (h : EventuallyStandard s) :
    exists T r, forall k : Nat,
      StandardHighwayFrom
        (flipCell (run s (T + 104 * k)) (run s (T + 104 * k)).pos)
        592 (rotatePoint r (-2, -2)) := h.late_flip_recovery hs

end LangtonsAnt
