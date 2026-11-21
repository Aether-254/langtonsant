import SingleBlackCheck

/-!
# Segmented single-black certificates

A long `checkSingleBlack` run keeps every intermediate 8 KB board in the kernel cache, so its
memory grows with the number of steps.  Here a run is split into segments.  Each segment is a
separate declaration (and module) that checks, by `decide +kernel`, that running a literal wide
state for `n` steps inside the window yields the next literal state exactly.  The final segment
checks the standard half-plane entry.  The literals come from an untrusted script; a wrong
literal only makes a check fail.
-/

namespace LangtonsAnt

def segRun : Nat -> WideState -> Option WideState
  | 0, s => some s
  | n + 1, s => if InWide s.pos then segRun n s.step else none

theorem segRun_sound {n : Nat} {s t : WideState} (h : segRun n s = some t) :
    t.toState = run s.toState n := by
  induction n generalizing s with
  | zero =>
    have heq : s = t := by simpa [segRun] using h
    exact congrArg WideState.toState heq.symm
  | succ n ih =>
    by_cases hp : InWide s.pos
    · simp only [segRun, hp, ite_true] at h
      have hh := ih h
      rw [WideState.toState_step _ hp] at hh
      change t.toState = run (run s.toState 1) n at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 n] using hh
    · simp [segRun, hp] at h

/-- `n` steps from `s` end exactly in the literal state `⟨b, p, d⟩`. -/
def checkSegment (n : Nat) (s : WideState) (b : Nat) (p : Point) (d : Direction) : Bool :=
  match segRun n s with
  | none => false
  | some t => (t.bits == b) && (t.pos == p) && (t.dir == d)

theorem checkSegment_sound {n : Nat} {s : WideState} {b : Nat} {p : Point} {d : Direction}
    (h : checkSegment n s b p d = true) :
    run s.toState n = (⟨b, p, d⟩ : WideState).toState := by
  unfold checkSegment at h
  cases hr : segRun n s with
  | none => simp [hr] at h
  | some t =>
    simp only [hr, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hb, hp⟩, hd⟩ := h
    rw [← segRun_sound hr]
    cases t
    simp only at hb hp hd
    subst hb; subst hp; subst hd
    rfl

theorem checkSegment_sound' {n : Nat} {s t : WideState}
    (h : checkSegment n s t.bits t.pos t.dir = true) : run s.toState n = t.toState := by
  have hh := checkSegment_sound h
  cases t
  exact hh

/-- Chain a reached state to the full run from the start. -/
theorem segment_chain {s u : State} {m n : Nat} {t : WideState}
    (h1 : run s m = u) (h2 : run u n = t.toState) : run s (m + n) = t.toState := by
  rw [run_add, h1, h2]

/-- Assemble: the start reaches the last literal state after `m` steps, and from there the
standard entry is reached after `n` more steps. -/
theorem singleBlack_of_segments {q : Point} {r : Direction} {w o : Point} {m n : Nat}
    {t : WideState}
    (hbox : (singleBlackFrame q r w).black.all (fun p => decide (InWide p)) = true)
    (hreach : run (singleBlackFrame q r w).toWide.toState m = t.toState)
    (hentry : checkWideEntry (weight o) (highwaySeed.translate o) n t = true) :
    EventuallyStandard (singleBlack q) := by
  have hbox' : forall p, p ∈ (singleBlackFrame q r w).black -> InWide p := fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp hbox p hp)
  have he := checkWideEntry_sound hentry
  rw [← hreach, ← run_add, FiniteState.toWide_toState _ hbox',
    FiniteState.toState_translate] at he
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
  exact ⟨m + n, rotatePoint r (-2, -2), diagonal_rotated_southwest r, hr⟩

end LangtonsAnt
