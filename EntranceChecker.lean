import HighwayEntrance

namespace LangtonsAnt

theorem checkAgreement_complete {cut : Int} {s t : FiniteState}
    (h : AgreesBelow cut s.toState t.toState) : checkAgreement cut s t = true := by
  simp only [checkAgreement, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨h.pos, h.dir⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro p _
  by_cases hp : weight p <= cut
  · have hc := h.board p hp
    change decide (p ∈ s.black) = decide (p ∈ t.black) at hc
    simp only [ite_eq_left hp, decide_eq_true_eq]
    exact decide_eq_decide.mp hc
  · simp [hp]

def FiniteState.rotate (r : Direction) (s : FiniteState) : FiniteState :=
  { black := s.black.map (rotatePoint r), pos := rotatePoint r s.pos, dir := rotateDir r s.dir }

theorem FiniteState.toState_rotate (r : Direction) (s : FiniteState) :
    (s.rotate r).toState = rotateState r s.toState := by
  have hb : (fun p => decide (p ∈ s.black.map (rotatePoint r))) =
      fun p => decide (rotatePoint (inverseRotation r) p ∈ s.black) := by
    funext p
    have hm : p ∈ s.black.map (rotatePoint r) ↔ rotatePoint (inverseRotation r) p ∈ s.black := by
      constructor
      · intro h
        obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
        rw [← heq, rotatePoint_inverse]
        exact hq
      · intro h
        exact List.mem_map.mpr ⟨rotatePoint (inverseRotation r) p, h, inverse_rotatePoint r p⟩
    simp only [hm]
  unfold FiniteState.rotate toState rotateState
  rw [hb]

def FiniteState.normalize (s : FiniteState) : FiniteState :=
  (s.translate (negPoint s.pos)).rotate (inverseRotation s.dir)

theorem FiniteState.toState_normalize (s : FiniteState) :
    s.normalize.toState = LangtonsAnt.normalize s.dir s.pos s.toState := by
  simp only [FiniteState.normalize, toState_rotate, toState_translate, LangtonsAnt.normalize]

/-- All four directions are checked by expressing the current pose in the standard frame. -/
def checkEntry (s : FiniteState) : Bool := checkAgreement 0 s.normalize highwaySeed

theorem checkEntry_iff (s : FiniteState) :
    checkEntry s = true ↔ EntryAt s.toState 0 s.dir s.pos := by
  constructor
  · intro h
    have hh := checkAgreement_sound h
    simpa only [EntryAt, run_zero, FiniteState.toState_normalize] using hh
  · intro h
    apply checkAgreement_complete
    simpa only [EntryAt, run_zero, FiniteState.toState_normalize] using h

theorem checkEntry_run_sound (s : FiniteState) (T : Nat)
    (h : checkEntry (s.run T) = true) :
    EntryAt s.toState T (s.run T).dir (s.run T).pos := by
  have hh := (checkEntry_iff (s.run T)).mp h
  simpa only [EntryAt, run_zero, FiniteState.toState_run] using hh

/-- Completeness does not supply a bound on when a successful check occurs. -/
theorem eventuallyStandard_iff_checkEntry (s : FiniteState) :
    EventuallyStandard s.toState ↔ exists T, checkEntry (s.run T) = true := by
  constructor
  · intro h
    obtain ⟨T, r, origin, hT⟩ := (eventuallyStandard_iff_enters s.finiteSupport).mp h
    refine ⟨T, (checkEntry_iff _).mpr ?_⟩
    have hh := hT.self_frame
    unfold EntryAt at hh ⊢
    rw [← FiniteState.toState_run s T] at hh
    exact hh
  · intro h
    obtain ⟨T, hT⟩ := h
    exact EventuallyEnters.standard ⟨T, _, _, checkEntry_run_sound s T hT⟩

/-- Search the inclusive time interval [0, fuel]; failure is only a finite observation. -/
def searchEntry : Nat -> FiniteState -> Option Nat
  | 0, s => if checkEntry s then some 0 else none
  | fuel + 1, s =>
    if checkEntry s then some 0 else (searchEntry fuel s.step).map (fun n => n + 1)

theorem FiniteState.run_step (s : FiniteState) (n : Nat) : s.step.run n = s.run (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FiniteState.run, ih]

theorem searchEntry_sound {s : FiniteState} {fuel T : Nat}
    (h : searchEntry fuel s = some T) : T <= fuel ∧ checkEntry (s.run T) = true := by
  induction fuel generalizing s T with
  | zero =>
    by_cases hc : checkEntry s = true
    · simp only [searchEntry, hc, ite_true, Option.some.injEq] at h
      subst T
      exact ⟨by omega, hc⟩
    · simp [searchEntry, hc] at h
  | succ fuel ih =>
    by_cases hc : checkEntry s = true
    · simp only [searchEntry, hc, ite_true, Option.some.injEq] at h
      subst T
      exact ⟨by omega, hc⟩
    · simp [searchEntry, hc] at h
      cases hr : searchEntry fuel s.step with
      | none => simp [hr] at h
      | some k =>
        have hk := ih hr
        have heq : k + 1 = T := by simpa [hr] using h
        clear h
        subst T
        exact ⟨by omega, by simpa only [FiniteState.run_step] using hk.2⟩

theorem searchEntry_complete {s : FiniteState} {fuel T : Nat}
    (hT : T <= fuel) (hc : checkEntry (s.run T) = true) :
    exists n, searchEntry fuel s = some n := by
  induction fuel generalizing s T with
  | zero =>
    have ht : T = 0 := by omega
    subst T
    exact ⟨0, by simp [searchEntry, FiniteState.run] at hc ⊢; exact hc⟩
  | succ fuel ih =>
    by_cases hnow : checkEntry s = true
    · exact ⟨0, by simp [searchEntry, hnow]⟩
    · cases T with
      | zero => exact False.elim (hnow hc)
      | succ k =>
        obtain ⟨n, hn⟩ := ih (s := s.step) (T := k) (by omega)
          (by simpa only [FiniteState.run_step] using hc)
        exact ⟨n + 1, by simp [searchEntry, hnow, hn]⟩

theorem eventuallyStandard_iff_search (s : FiniteState) :
    EventuallyStandard s.toState ↔ exists fuel T, searchEntry fuel s = some T := by
  rw [eventuallyStandard_iff_checkEntry]
  constructor
  · intro h
    obtain ⟨T, hT⟩ := h
    obtain ⟨n, hn⟩ := searchEntry_complete (by omega : T <= T) hT
    exact ⟨T, n, hn⟩
  · intro h
    obtain ⟨fuel, T, hT⟩ := h
    exact ⟨T, (searchEntry_sound hT).2⟩

theorem finiteSupport_representable (s : State) (h : FiniteSupport s.board) :
    exists f : FiniteState, f.toState = s := by
  obtain ⟨cells, hc⟩ := h
  refine ⟨⟨cells.filter s.board, s.pos, s.dir⟩, ?_⟩
  have hb : (fun p => decide (p ∈ cells.filter s.board)) = s.board := by
    funext p
    cases hp : s.board p
    · simp [hp]
    · simp [hc p hp, hp]
  change ({ board := _, pos := s.pos, dir := s.dir } : State) = s
  rw [hb]

/-- This is still an open proposition, not an assumed termination proof. -/
def DetectorEventuallySucceeds : Prop :=
  forall s : FiniteState, exists fuel T, searchEntry fuel s = some T

theorem highwayConjecture_iff_detectorEventuallySucceeds :
    HighwayConjecture ↔ DetectorEventuallySucceeds := by
  constructor
  · intro h s
    exact (eventuallyStandard_iff_search s).mp (h s.toState s.finiteSupport)
  · intro h s hs
    obtain ⟨f, hf⟩ := finiteSupport_representable s hs
    have hh := (eventuallyStandard_iff_search f).mpr (h f)
    simpa only [hf, EventuallyStandard] using hh

end LangtonsAnt
