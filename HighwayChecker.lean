import Highway
import FiniteAnt

namespace LangtonsAnt

def FiniteState.translate (v : Point) (s : FiniteState) : FiniteState :=
  { black := s.black.map (addPoint v), pos := addPoint v s.pos, dir := s.dir }

theorem FiniteState.toState_translate (v : Point) (s : FiniteState) :
    (s.translate v).toState = LangtonsAnt.translate v s.toState := by
  have hb : (fun p => decide (p ∈ s.black.map (addPoint v))) =
      fun p => decide (subPoint p v ∈ s.black) := by
    funext p
    have hm : p ∈ s.black.map (addPoint v) ↔ subPoint p v ∈ s.black := by
      constructor
      · intro h
        obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
        rw [← heq, subPoint_addPoint]
        exact hq
      · intro h
        exact List.mem_map.mpr ⟨subPoint p v, h, addPoint_subPoint v p⟩
    simp only [hm]
  unfold FiniteState.translate toState LangtonsAnt.translate
  rw [hb]

def checkAgreement (cut : Int) (s t : FiniteState) : Bool :=
  (s.pos == t.pos) && (s.dir == t.dir) &&
  (s.black ++ t.black).all (fun p =>
    if weight p <= cut then decide ((p ∈ s.black) ↔ (p ∈ t.black)) else true)

theorem checkAgreement_sound {cut : Int} {s t : FiniteState}
    (h : checkAgreement cut s t = true) : AgreesBelow cut s.toState t.toState := by
  simp only [checkAgreement, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  intro p hp
  change decide (p ∈ s.black) = decide (p ∈ t.black)
  by_cases hm : p ∈ s.black ++ t.black
  · have hh := List.all_eq_true.mp h.2 p hm
    simp only [ite_eq_left hp, decide_eq_true_eq] at hh
    simp only [hh]
  · have hs : p ∉ s.black := fun hs => hm (List.mem_append_left _ hs)
    have ht : p ∉ t.black := fun ht => hm (List.mem_append_right _ ht)
    simp [hs, ht]

def checkBounded (cut : Int) : Nat -> FiniteState -> Bool
  | 0, _ => true
  | n + 1, s => decide (weight s.pos <= cut) && checkBounded cut n s.step

theorem checkBounded_sound {cut : Int} {n : Nat} {s : FiniteState}
    (h : checkBounded cut n s = true) :
    forall j, j < n -> weight (run s.toState j).pos <= cut := by
  induction n generalizing s with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkBounded, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j =>
      have hh := ih h.2 j (by omega)
      rw [FiniteState.toState_step] at hh
      change weight (run (run s.toState 1) j).pos <= cut at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 j] using hh

def checkCertificate (s : FiniteState) (P : Nat) (v : Point) (cut : Int) : Bool :=
  decide (0 < P) && decide (weight v <= 0) && checkBounded cut P s &&
    checkAgreement (cut + weight v) (s.run P) (s.translate v)

theorem checkCertificate_sound {s : FiniteState} {P : Nat} {v : Point} {cut : Int}
    (h : checkCertificate s P v cut = true) : HighwayCertificate s.toState P v cut := by
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, checkBounded_sound h.1.2, ?_⟩
  have hr := checkAgreement_sound h.2
  simpa only [FiniteState.toState_run, FiniteState.toState_translate] using hr

def checkTrace : FiniteState -> List Bool -> Bool
  | _, [] => true
  | s, c :: cs => (decide (s.pos ∈ s.black) == c) && checkTrace s.step cs

theorem checkTrace_sound {s : FiniteState} {word : List Bool}
    (h : checkTrace s word = true) :
    forall j, j < word.length -> readColor s.toState j = word[j]?.getD false := by
  induction word generalizing s with
  | nil => intro j hj; simp at hj
  | cons c cs ih =>
    simp only [checkTrace, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa [readColor, run, FiniteState.toState] using h.1
    | succ j =>
      have hh := ih h.2 j (by simpa using hj)
      rw [FiniteState.toState_step] at hh
      change readColor (run s.toState 1) j = _ at hh
      unfold readColor at hh ⊢
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 j, List.getElem?_cons_succ] using hh

end LangtonsAnt
