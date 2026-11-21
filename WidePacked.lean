import FiniteAnt
import HighwayChecker

/-!
# A wider packed window with a fast half-plane agreement check

`PackedAnt.lean` uses a fixed `128 × 128` window.  Some finite computations (single black cells
in the blank transient, recoveries that reach the blank remnants) need more room.  This file
gives a `256 × 256` window `[-128,128)^2` with the same soundness guarantees: a run is only
accepted while every visited cell is inside the window, nothing wraps or is clamped.

The half-plane agreement `AgreesBelow cut` is checked with a bit mask instead of a cell-by-cell
scan: `halfMask cut` has exactly the window cells of weight `<= cut` set, and agreement holds
when `(s.bits ^^^ target.bits) &&& halfMask cut = 0` and the target lies in the window.
-/

namespace LangtonsAnt

def InWide (p : Point) : Prop :=
  -128 <= p.1 ∧ p.1 < 128 ∧ -128 <= p.2 ∧ p.2 < 128

instance (p : Point) : Decidable (InWide p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def wideIndex (p : Point) : Nat := (p.1 + 128).toNat * 256 + (p.2 + 128).toNat

theorem wideIndex_injective {p q : Point} (hp : InWide p) (hq : InWide q)
    (h : wideIndex p = wideIndex q) : p = q := by
  simp only [InWide] at hp hq
  simp only [wideIndex] at h
  apply Prod.ext <;> omega

def wideBoard (bits : Nat) : Board :=
  fun p => if InWide p then bits.testBit (wideIndex p) else false

structure WideState where
  bits : Nat
  pos : Point
  dir : Direction

def WideState.toState (s : WideState) : State :=
  ⟨wideBoard s.bits, s.pos, s.dir⟩

def WideState.step (s : WideState) : WideState :=
  let d := turn (s.bits.testBit (wideIndex s.pos)) s.dir
  { bits := s.bits ^^^ (2 ^ wideIndex s.pos), pos := move s.pos d, dir := d }

theorem wideBoard_flip (bits : Nat) (p : Point) (hp : InWide p) :
    wideBoard (bits ^^^ (2 ^ wideIndex p)) = flip (wideBoard bits) p := by
  funext q
  by_cases hq : InWide q
  · have heq : wideIndex p = wideIndex q ↔ q = p :=
      ⟨fun h => (wideIndex_injective hp hq h).symm, fun h => by rw [h]⟩
    simp only [wideBoard, ite_eq_left hq, Nat.testBit_xor, Nat.testBit_two_pow, heq, flip]
    by_cases h : q = p <;> simp [h]
  · have hne : q ≠ p := fun h => hq (h ▸ hp)
    simp [wideBoard, hq, flip, hne]

theorem WideState.toState_step (s : WideState) (hp : InWide s.pos) :
    s.step.toState = LangtonsAnt.step s.toState := by
  simp [WideState.step, toState, LangtonsAnt.step, wideBoard_flip _ _ hp, wideBoard, hp]

/-! ## Encoding finite cell lists -/

def wideCells : List Point -> Nat
  | [] => 0
  | p :: ps => wideCells ps ||| (2 ^ wideIndex p)

theorem wideBoard_wideCells (cells : List Point)
    (hbox : forall p, p ∈ cells -> InWide p) :
    wideBoard (wideCells cells) = fun p => decide (p ∈ cells) := by
  induction cells with
  | nil => funext p; simp [wideCells, wideBoard]
  | cons p ps ih =>
    have hp := hbox p (by simp)
    have ht := ih (fun q hq => hbox q (by simp [hq]))
    funext q
    by_cases hq : InWide q
    · have heq : wideIndex p = wideIndex q ↔ q = p :=
        ⟨fun h => (wideIndex_injective hp hq h).symm, fun h => by rw [h]⟩
      have hh := congrFun ht q
      simp only [wideBoard, ite_eq_left hq] at hh
      simp [wideCells, wideBoard, hq, Nat.testBit_or, Nat.testBit_two_pow, heq, hh, Bool.or_comm]
    · have hn : q ∉ p :: ps := fun h => hq (hbox q h)
      simp [wideBoard, hq, hn]

def FiniteState.toWide (s : FiniteState) : WideState :=
  ⟨wideCells s.black, s.pos, s.dir⟩

theorem FiniteState.toWide_toState (s : FiniteState)
    (hbox : forall p, p ∈ s.black -> InWide p) : s.toWide.toState = s.toState := by
  simp only [toWide, WideState.toState, toState, wideBoard_wideCells s.black hbox]

/-! ## Half-plane masks -/

/-- Row `x0` (window column index) of the mask: cells with `y0 < len`. -/
def halfRowLen (cut : Int) (x0 : Nat) : Nat := min 256 (cut + 257 - (x0 : Int)).toNat

def halfMaskAux (cut : Int) : Nat -> Nat
  | 0 => 0
  | n + 1 => halfMaskAux cut n ||| ((2 ^ halfRowLen cut n - 1) <<< (n * 256))

def halfMask (cut : Int) : Nat := halfMaskAux cut 256

theorem halfMaskAux_testBit (cut : Int) (n x0 y0 : Nat) (hx : x0 < n) (_hy : y0 < 256)
    (hl : y0 < halfRowLen cut x0) : (halfMaskAux cut n).testBit (x0 * 256 + y0) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [halfMaskAux, Nat.testBit_or, Bool.or_eq_true]
    by_cases hlt : x0 < n
    · exact Or.inl (ih hlt)
    · have he : x0 = n := by omega
      subst he
      right
      rw [Nat.testBit_shiftLeft]
      simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and,
        Nat.add_sub_cancel_left, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      exact hl

theorem halfMask_testBit {cut : Int} {p : Point} (hp : InWide p) (hw : weight p <= cut) :
    (halfMask cut).testBit (wideIndex p) = true := by
  simp only [InWide] at hp
  simp only [weight] at hw
  unfold halfMask wideIndex
  apply halfMaskAux_testBit cut 256 _ _ (by omega) (by omega)
  unfold halfRowLen
  omega

/-- Agreement on the half-plane `weight <= cut` with a finite target, by one masked xor. -/
def checkWideAgreement (cut : Int) (s : WideState) (t : FiniteState) : Bool :=
  (s.pos == t.pos) && (s.dir == t.dir) && t.black.all (fun p => decide (InWide p)) &&
    ((s.bits ^^^ wideCells t.black) &&& halfMask cut) == 0

theorem checkWideAgreement_sound {cut : Int} {s : WideState} {t : FiniteState}
    (h : checkWideAgreement cut s t = true) : AgreesBelow cut s.toState t.toState := by
  simp only [checkWideAgreement, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hpos, hdir⟩, hbox⟩, hmask⟩ := h
  have hbox' : forall p, p ∈ t.black -> InWide p := fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp hbox p hp)
  refine ⟨hpos, hdir, ?_⟩
  intro p hp
  have ht : t.toState.board p = wideBoard (wideCells t.black) p := by
    rw [wideBoard_wideCells t.black hbox']
    rfl
  rw [ht]
  change wideBoard s.bits p = wideBoard (wideCells t.black) p
  by_cases hin : InWide p
  · simp only [wideBoard, hin, ite_true]
    have hm := halfMask_testBit hin hp
    have hz := congrArg (fun n => n.testBit (wideIndex p)) hmask
    simp only [Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Nat.zero_testBit] at hz
    cases ha : s.bits.testBit (wideIndex p) <;>
      cases hb : (wideCells t.black).testBit (wideIndex p) <;> simp_all
  · simp [wideBoard, hin]

/-! ## Checked runs -/

/-- Run `n` steps while every visited cell is in the window, then check the entry. -/
def checkWideEntry (cut : Int) (target : FiniteState) : Nat -> WideState -> Bool
  | 0, s => checkWideAgreement cut s target
  | n + 1, s => decide (InWide s.pos) && checkWideEntry cut target n s.step

theorem checkWideEntry_sound {cut : Int} {target : FiniteState} {n : Nat} {s : WideState}
    (h : checkWideEntry cut target n s = true) :
    AgreesBelow cut (run s.toState n) target.toState := by
  induction n generalizing s with
  | zero => exact checkWideAgreement_sound h
  | succ n ih =>
    simp only [checkWideEntry, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh := ih h.2
    rw [WideState.toState_step _ h.1] at hh
    change AgreesBelow cut (run (run s.toState 1) n) target.toState at hh
    rw [← run_add, Nat.add_comm 1 n] at hh
    exact hh

end LangtonsAnt
