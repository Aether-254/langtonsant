import Phase49P2

/-!
# Segmented form of the phase-49 prefix check

The single 52421-step check `checkTrailPrefix` exhausts memory, because the kernel caches every
intermediate state.  Here the run is split into segments, each its own module: a segment checks,
for `n` steps, the box and the guard at every step, and that the end state equals a literal
`PackedState`.  The literals come from an untrusted script; a wrong literal only fails a check.
-/

namespace LangtonsAnt

/-- The guard of the phase-49 prefix: safe for the strip argument and off the junk shadow. -/
def g49 (p : Point) : Bool :=
  decide (TrailSafe (trailUnframePoint p)) && avoidJunk2 (trailUnframePoint p)

def checkTrailSeg (guard : Point -> Bool) : Nat -> PackedState -> PackedState -> Bool
  | 0, s, t => (s.bits == t.bits) && (s.pos == t.pos) && (s.dir == t.dir)
  | n + 1, s, t => decide (InBox s.pos) && guard s.pos && checkTrailSeg guard n s.step t

theorem checkTrailSeg_sound {guard : Point -> Bool} {n : Nat} {s t : PackedState}
    (h : checkTrailSeg guard n s t = true) :
    (forall j, j < n -> guard (run s.toState j).pos = true) ∧ run s.toState n = t.toState := by
  induction n generalizing s with
  | zero =>
    simp only [checkTrailSeg, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hb, hp⟩, hd⟩ := h
    refine ⟨fun j hj => by omega, ?_⟩
    cases s; cases t
    simp only at hb hp hd
    subst hb; subst hp; subst hd
    rfl
  | succ n ih =>
    simp only [checkTrailSeg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, he⟩ := ih h.2
    have hs := PackedState.toState_step s h.1.1
    rw [hs] at hb he
    have hr : forall j, run (step s.toState) j = run s.toState (j + 1) := by
      intro j
      change run (run s.toState 1) j = _
      rw [← run_add, Nat.add_comm 1 j]
    refine ⟨?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact h.1.2
      | succ j => simpa only [hr] using hb j (by omega)
    · simpa only [hr] using he

/-- Shift a guard statement along a reached prefix. -/
theorem guard_shift {guard : Point -> Bool} {X : State} {S : PackedState} {a n : Nat}
    (hreach : run X a = S.toState) (hg : forall j, j < n -> guard (run S.toState j).pos = true) :
    forall j, j < n -> guard (run X (a + j)).pos = true := by
  intro j hj
  rw [run_add, hreach]
  exact hg j hj

end LangtonsAnt
