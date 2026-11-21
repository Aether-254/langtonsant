import HighwayChecker

namespace LangtonsAnt

/-- A checked computation window, never a torus or a boundary rule. -/
def InBox (p : Point) : Prop :=
  -64 <= p.1 ∧ p.1 < 64 ∧ -64 <= p.2 ∧ p.2 < 64

instance (p : Point) : Decidable (InBox p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def bitIndex (p : Point) : Nat := (p.1 + 64).toNat * 128 + (p.2 + 64).toNat

theorem bitIndex_injective {p q : Point} (hp : InBox p) (hq : InBox q)
    (h : bitIndex p = bitIndex q) : p = q := by
  simp only [InBox] at hp hq
  simp only [bitIndex] at h
  apply Prod.ext <;> omega

def packedBoard (bits : Nat) : Board :=
  fun p => if InBox p then bits.testBit (bitIndex p) else false

structure PackedState where
  bits : Nat
  pos : Point
  dir : Direction

def PackedState.toState (s : PackedState) : State :=
  ⟨packedBoard s.bits, s.pos, s.dir⟩

def PackedState.step (s : PackedState) : PackedState :=
  let d := turn (s.bits.testBit (bitIndex s.pos)) s.dir
  { bits := s.bits ^^^ (2 ^ bitIndex s.pos), pos := move s.pos d, dir := d }

theorem packedBoard_flip (bits : Nat) (p : Point) (hp : InBox p) :
    packedBoard (bits ^^^ (2 ^ bitIndex p)) = flip (packedBoard bits) p := by
  funext q
  by_cases hq : InBox q
  · have heq : bitIndex p = bitIndex q ↔ q = p :=
      ⟨fun h => (bitIndex_injective hp hq h).symm, fun h => by rw [h]⟩
    simp only [packedBoard, ite_eq_left hq, Nat.testBit_xor, Nat.testBit_two_pow, heq, flip]
    by_cases h : q = p <;> simp [h]
  · have hne : q ≠ p := fun h => hq (h ▸ hp)
    simp [packedBoard, hq, flip, hne]

theorem PackedState.toState_step (s : PackedState) (hp : InBox s.pos) :
    s.step.toState = LangtonsAnt.step s.toState := by
  simp [PackedState.step, toState, LangtonsAnt.step, packedBoard_flip _ _ hp,
    packedBoard, hp]

/-- Failure means a visited cell left the checked window, so no claim is made. -/
def packedRun : Nat -> PackedState -> Option PackedState
  | 0, s => some s
  | n + 1, s => if InBox s.pos then packedRun n s.step else none

theorem packedRun_sound {n : Nat} {s t : PackedState} (h : packedRun n s = some t) :
    t.toState = run s.toState n := by
  induction n generalizing s with
  | zero =>
    have heq : s = t := by simpa [packedRun] using h
    exact congrArg PackedState.toState heq.symm
  | succ n ih =>
    by_cases hp : InBox s.pos
    · simp only [packedRun, ite_eq_left hp] at h
      have hh := ih h
      rw [PackedState.toState_step _ hp] at hh
      change t.toState = run (run s.toState 1) n at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 n] using hh
    · simp [packedRun, hp] at h

theorem packedRun_inBox {n : Nat} {s t : PackedState} (h : packedRun n s = some t) :
    forall j, j < n -> InBox (run s.toState j).pos := by
  induction n generalizing s with
  | zero => intro j hj; omega
  | succ n ih =>
    by_cases hp : InBox s.pos
    · simp only [packedRun, ite_eq_left hp] at h
      intro j hj
      cases j with
      | zero => exact hp
      | succ j =>
        have hh := ih h j (by omega)
        rw [PackedState.toState_step _ hp] at hh
        change InBox (run (run s.toState 1) j).pos at hh
        rw [← run_add] at hh
        simpa only [Nat.add_comm 1 j] using hh
    · simp [packedRun, hp] at h

def packedBlank : PackedState := ⟨0, (0, 0), .north⟩

@[simp] theorem packedBlank_toState : packedBlank.toState = blank := by
  have hb : packedBoard 0 = fun _ => false := by
    funext p
    simp [packedBoard]
  unfold PackedState.toState packedBlank blank
  rw [hb]

def packedTrace : PackedState -> List Bool -> Bool
  | _, [] => true
  | s, c :: cs =>
    decide (InBox s.pos) && (s.bits.testBit (bitIndex s.pos) == c) && packedTrace s.step cs

theorem packedTrace_sound {s : PackedState} {word : List Bool}
    (h : packedTrace s word = true) :
    forall j, j < word.length -> readColor s.toState j = word[j]?.getD false := by
  induction word generalizing s with
  | nil => intro j hj; simp at hj
  | cons c cs ih =>
    simp only [packedTrace, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa [readColor, run, PackedState.toState, packedBoard, h.1.1] using h.1.2
    | succ j =>
      have hh := ih h.2 j (by simpa using hj)
      rw [PackedState.toState_step _ h.1.1] at hh
      change readColor (run s.toState 1) j = _ at hh
      unfold readColor at hh ⊢
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 j, List.getElem?_cons_succ] using hh

def checkPackedTraceAfter (n : Nat) (s : PackedState) (word : List Bool) : Bool :=
  match packedRun n s with
  | none => false
  | some t => packedTrace t word

theorem checkPackedTraceAfter_sound {n : Nat} {s : PackedState} {word : List Bool}
    (h : checkPackedTraceAfter n s word = true) :
    forall j, j < word.length -> readColor s.toState (n + j) = word[j]?.getD false := by
  unfold checkPackedTraceAfter at h
  cases hr : packedRun n s with
  | none => simp [hr] at h
  | some t =>
    simp only [hr] at h
    intro j hj
    have hh := packedTrace_sound h j hj
    rw [packedRun_sound hr] at hh
    simpa only [readColor, ← run_add] using hh

def boxPoints : List Point :=
  (List.range 128).flatMap (fun (x : Nat) => (List.range 128).map
    (fun (y : Nat) => ((x : Int) - 64, (y : Int) - 64)))

theorem mem_boxPoints {p : Point} (hp : InBox p) : p ∈ boxPoints := by
  simp only [InBox] at hp
  apply List.mem_flatMap.mpr
  refine ⟨(p.1 + 64).toNat, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_map.mpr
  refine ⟨(p.2 + 64).toNat, List.mem_range.mpr (by omega), ?_⟩
  apply Prod.ext <;> simp <;> omega

def checkPackedAgreement (cut : Int) (s : PackedState) (t : FiniteState) : Bool :=
  (s.pos == t.pos) && (s.dir == t.dir) &&
  t.black.all (fun p => decide (InBox p)) &&
  boxPoints.all (fun p => if weight p <= cut then
    s.bits.testBit (bitIndex p) == decide (p ∈ t.black) else true)

theorem checkPackedAgreement_sound {cut : Int} {s : PackedState} {t : FiniteState}
    (h : checkPackedAgreement cut s t = true) : AgreesBelow cut s.toState t.toState := by
  simp only [checkPackedAgreement, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, ?_⟩
  intro p hp
  by_cases hbox : InBox p
  · have hh := List.all_eq_true.mp h.2 p (mem_boxPoints hbox)
    simpa [PackedState.toState, packedBoard, hbox, FiniteState.toState, hp] using hh
  · have hnot : p ∉ t.black := by
      intro hm
      have hh := List.all_eq_true.mp h.1.2 p hm
      exact hbox (of_decide_eq_true hh)
    simp [PackedState.toState, packedBoard, hbox, FiniteState.toState, hnot]

def checkPackedEntry (n : Nat) (s : PackedState) (cut : Int) (target : FiniteState) : Bool :=
  match packedRun n s with
  | none => false
  | some t => checkPackedAgreement cut t target

theorem checkPackedEntry_sound {n : Nat} {s : PackedState} {cut : Int} {target : FiniteState}
    (h : checkPackedEntry n s cut target = true) :
    AgreesBelow cut (run s.toState n) target.toState := by
  unfold checkPackedEntry at h
  cases hr : packedRun n s with
  | none => simp [hr] at h
  | some t =>
    simp only [hr] at h
    have hh := checkPackedAgreement_sound h
    simpa only [packedRun_sound hr] using hh

theorem checkPackedEntry_inBox {n : Nat} {s : PackedState} {cut : Int} {target : FiniteState}
    (h : checkPackedEntry n s cut target = true) :
    forall j, j < n -> InBox (run s.toState j).pos := by
  unfold checkPackedEntry at h
  cases hr : packedRun n s with
  | none => simp [hr] at h
  | some t => exact packedRun_inBox hr

end LangtonsAnt
