import TrajectoryCoupling

namespace LangtonsAnt

/-- A single, finite-to-check entry condition, in any translated and rotated frame. -/
def EntryAt (s : State) (T : Nat) (r : Direction) (origin : Point) : Prop :=
  AgreesBelow 0 (normalize r origin (run s T)) highwaySeed.toState

def EventuallyEnters (s : State) : Prop :=
  exists T r origin, EntryAt s T r origin

def EventuallyStandard (s : State) : Prop :=
  exists T v, DiagonalDrift v ∧ StandardHighwayFrom s T v

theorem EntryAt.pose_fields {s : State} {T : Nat} {r : Direction} {origin : Point}
    (h : EntryAt s T r origin) : (run s T).pos = origin ∧ (run s T).dir = r := by
  have hp := congrArg State.pos (pose_normalize r origin (run s T))
  have hd := congrArg State.dir (pose_normalize r origin (run s T))
  change addPoint origin (rotatePoint r (normalize r origin (run s T)).pos) = (run s T).pos at hp
  change rotateDir r (normalize r origin (run s T)).dir = (run s T).dir at hd
  have h' : AgreesBelow 0 (normalize r origin (run s T)) highwaySeed.toState := h
  rw [h'.pos] at hp
  rw [h'.dir] at hd
  change addPoint origin (rotatePoint r (0, 0)) = _ at hp
  change rotateDir r .north = _ at hd
  exact ⟨(by simpa using hp.symm), (by simpa using hd.symm)⟩

theorem EntryAt.self_frame {s : State} {T : Nat} {r : Direction} {origin : Point}
    (h : EntryAt s T r origin) : EntryAt s T (run s T).dir (run s T).pos := by
  rw [h.pose_fields.1, h.pose_fields.2]
  exact h

theorem normalize_pose_at_self (s : State) :
    (normalize s.dir s.pos s).pos = (0, 0) ∧
    (normalize s.dir s.pos s).dir = .north := by
  have hp : addPoint (negPoint s.pos) s.pos = (0, 0) := by
    apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
  constructor
  · change rotatePoint (inverseRotation s.dir) (addPoint (negPoint s.pos) s.pos) = _
    rw [hp, rotatePoint_zero]
  · change rotateDir (inverseRotation s.dir) s.dir = _
    cases s.dir <;> rfl

theorem AgreesBelow.normalize_translate {s : State} {v : Point}
    (h : AgreesBelow (weight v) s (LangtonsAnt.translate v highwaySeed.toState)) :
    AgreesBelow 0 (LangtonsAnt.translate (negPoint v) s) highwaySeed.toState := by
  have hh := h.translate (negPoint v)
  have hz : addPoint (negPoint v) v = (0, 0) := by
    apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
  have hw : weight v + weight (negPoint v) = 0 := by simp [weight, negPoint]; omega
  rw [translate_add, hz, translate_zero, hw] at hh
  exact hh

theorem EntryAt.standard {s : State} {T : Nat} {r : Direction} {origin : Point}
    (h : EntryAt s T r origin) :
    StandardHighwayFrom s T (rotatePoint r (-2, -2)) := by
  have hn : StandardHighwayFrom (normalize r origin (run s T)) 0 (-2, -2) := by
    apply standard_highway_of_entry (origin := (0, 0))
    simpa only [EntryAt, run_zero, weight, Int.zero_add, translate_zero] using h
  have hp := (hn.rotate r).translate origin
  change StandardHighwayFrom (pose r origin (normalize r origin (run s T))) 0 _ at hp
  rw [pose_normalize] at hp
  refine ⟨highwayFrom_run hp.1, ?_⟩
  intro n
  have hh := hp.2 n
  simpa only [Nat.zero_add, readColor, ← run_add] using hh

theorem EventuallyEnters.standard {s : State} (h : EventuallyEnters s) : EventuallyStandard s := by
  obtain ⟨T, r, origin, hentry⟩ := h
  exact ⟨T, rotatePoint r (-2, -2), diagonal_rotated_southwest r, hentry.standard⟩

theorem normalize_shift (r : Direction) (origin v : Point) (s : State) :
    translate (negPoint v) (normalize r origin s) =
      normalize r (addPoint origin (rotatePoint r v)) s := by
  have hboard :
      (fun p => s.board (subPoint (rotatePoint r (subPoint p (negPoint v))) (negPoint origin))) =
      fun p => s.board (subPoint (rotatePoint r p) (negPoint (addPoint origin (rotatePoint r v)))) := by
    funext p
    congr 1
    cases r <;> apply Prod.ext <;>
      simp [subPoint, negPoint, addPoint, rotatePoint] <;> omega
  have hpos : addPoint (negPoint v) (rotatePoint (inverseRotation r) (addPoint (negPoint origin) s.pos)) =
      rotatePoint (inverseRotation r) (addPoint (negPoint (addPoint origin (rotatePoint r v))) s.pos) := by
    cases r <;> apply Prod.ext <;>
      simp [negPoint, addPoint, rotatePoint, inverseRotation] <;> omega
  have hi : inverseRotation (inverseRotation r) = r := by cases r <;> rfl
  simp only [normalize, translate, rotateState, hi, hboard, hpos]

/-- Completeness uses finite support: all initial disagreement eventually lies behind the front. -/
theorem EventuallyStandard.enters {s : State} (hs : FiniteSupport s.board)
    (h : EventuallyStandard s) : EventuallyEnters s := by
  obtain ⟨T, v, _, hstandard⟩ := h
  let t := run s T
  let r := t.dir
  let origin := t.pos
  let u := normalize r origin t
  have hu : FiniteSupport u.board := finiteSupport_normalize (finiteSupport_run s hs T) r origin
  have hp := normalize_pose_at_self t
  have hc : forall n, readColor u n = standardColor n := by
    intro n
    rw [normalize_readColor]
    simpa only [t, readColor, ← run_add] using hstandard.2 n
  obtain ⟨k, hk⟩ := standard_reads_eventually_match hu hp.1 hp.2 hc
  have hn := hk.normalize_translate
  rw [normalize_run, normalize_shift] at hn
  refine ⟨T + 104 * k, r, addPoint origin (rotatePoint r (offset (-2, -2) k)), ?_⟩
  simpa only [EntryAt, t, ← run_add] using hn

theorem eventuallyStandard_iff_enters {s : State} (hs : FiniteSupport s.board) :
    EventuallyStandard s ↔ EventuallyEnters s :=
  ⟨EventuallyStandard.enters hs, EventuallyEnters.standard⟩

/-- The unresolved global entrance assertion, equivalent to the original conjecture. -/
def EntranceConjecture : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyEnters s

theorem highwayConjecture_iff_entranceConjecture : HighwayConjecture ↔ EntranceConjecture := by
  constructor
  · intro h s hs
    exact (eventuallyStandard_iff_enters hs).mp (h s hs)
  · intro h s hs
    exact (eventuallyStandard_iff_enters hs).mpr (h s hs)

/-- The complete standard read word alone determines the highway once the pose is fixed. -/
theorem standard_of_trace {s : State} {T : Nat}
    (h : forall n, readColor s (T + n) = standardColor n) :
    StandardHighwayFrom s T (rotatePoint (run s T).dir (-2, -2)) := by
  let t := run s T
  have hp := normalize_pose_at_self t
  have hc : forall n, readColor (normalize t.dir t.pos t) n = standardColor n := by
    intro n
    rw [normalize_readColor]
    simpa only [t, readColor, ← run_add] using h n
  have hh := standard_reads_highway hp.1 hp.2 hc
  have hg := (hh.rotate t.dir).translate t.pos
  change StandardHighwayFrom (pose t.dir t.pos (normalize t.dir t.pos t)) 0 _ at hg
  rw [pose_normalize] at hg
  exact ⟨highwayFrom_run hg.1, h⟩

def StandardTraceConjecture : Prop :=
  forall s : State, FiniteSupport s.board ->
    exists T, forall n, readColor s (T + n) = standardColor n

theorem highwayConjecture_iff_standardTraceConjecture :
    HighwayConjecture ↔ StandardTraceConjecture := by
  constructor
  · intro h s hs
    obtain ⟨T, v, _, hT⟩ := h s hs
    exact ⟨T, hT.2⟩
  · intro h s hs
    obtain ⟨T, hT⟩ := h s hs
    exact ⟨T, rotatePoint (run s T).dir (-2, -2), diagonal_rotated_southwest _, standard_of_trace hT⟩

end LangtonsAnt
