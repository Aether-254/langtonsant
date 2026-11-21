import WidePacked

/-!
# A persistent binary-tree board for low-memory kernel computations

A `WideState` keeps the whole `256 × 256` window in one natural number, so every step creates
several 8 KB numbers, all of which the kernel caches during `decide +kernel`.  Here the window
is a binary tree of depth 16 over `wideIndex`, most-significant bit first; a uniform subtree is a
single leaf and is expanded only along the path of a flip.  One step creates at most 16 nodes.

`toBits` converts a tree back to the bit encoding once, so the final half-plane agreement reuses
`checkWideAgreement`.  Soundness is proved against the original model; no step is trusted.
-/

namespace LangtonsAnt

inductive BT where
  | lf (b : Bool)
  | nd (l r : BT)

/-- Read index `i` in a tree of depth `d` (indices `< 2^d`). -/
def BT.get : BT -> Nat -> Nat -> Bool
  | .lf b, _, _ => b
  | .nd l _, i, 0 => l.get i 0
  | .nd l r, i, d + 1 => if i < 2 ^ d then l.get i d else r.get (i - 2 ^ d) d

/-- Flip index `i` in a tree of depth `d`, expanding uniform leaves on the way. -/
def BT.flip : BT -> Nat -> Nat -> BT
  | .lf b, _, 0 => .lf (!b)
  | .lf b, i, d + 1 =>
    if i < 2 ^ d then .nd ((BT.lf b).flip i d) (.lf b) else .nd (.lf b) ((BT.lf b).flip (i - 2 ^ d) d)
  | .nd l _, i, 0 => .lf (!(l.get i 0))
  | .nd l r, i, d + 1 => if i < 2 ^ d then .nd (l.flip i d) r else .nd l (r.flip (i - 2 ^ d) d)

theorem BT.get_flip (t : BT) (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    (t.flip i d).get j d = if i = j then !(t.get j d) else t.get j d := by
  induction d generalizing t i j with
  | zero =>
    have hi0 : i = 0 := by simp at hi; omega
    have hj0 : j = 0 := by simp at hj; omega
    subst hi0; subst hj0
    cases t <;> simp [BT.flip, BT.get]
  | succ d ih =>
    have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    cases t with
    | lf b =>
      by_cases hil : i < 2 ^ d <;> by_cases hjl : j < 2 ^ d
      · simp only [BT.flip, hil, ite_true, BT.get, hjl]
        rw [ih _ _ _ hil hjl]
        simp [BT.get]
      · simp only [BT.flip, hil, ite_true, BT.get, hjl, ite_false]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [BT.flip, hil, ite_false, BT.get, hjl, ite_true]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [BT.flip, hil, ite_false, BT.get, hjl]
        rw [ih _ _ _ (by omega) (by omega)]
        have he : (i - 2 ^ d = j - 2 ^ d) ↔ i = j := by omega
        simp [BT.get, he]
    | nd l r =>
      by_cases hil : i < 2 ^ d <;> by_cases hjl : j < 2 ^ d
      · simp only [BT.flip, hil, ite_true, BT.get, hjl]
        exact ih _ _ _ hil hjl
      · simp only [BT.flip, hil, ite_true, BT.get, hjl, ite_false]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [BT.flip, hil, ite_false, BT.get, hjl, ite_true]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [BT.flip, hil, ite_false, BT.get, hjl]
        rw [ih _ _ _ (by omega) (by omega)]
        have he : (i - 2 ^ d = j - 2 ^ d) ↔ i = j := by omega
        simp [he]

/-- Bit encoding of a tree of depth `d`: bit `i` is the leaf at index `i`. -/
def BT.toBits : BT -> Nat -> Nat
  | .lf b, d => if b then 2 ^ (2 ^ d) - 1 else 0
  | .nd l _, 0 => l.toBits 0
  | .nd l r, d + 1 => l.toBits d ||| (r.toBits d <<< (2 ^ d))

theorem BT.toBits_testBit_high (t : BT) (d i : Nat) (hi : 2 ^ d <= i) :
    (t.toBits d).testBit i = false := by
  induction d generalizing t i with
  | zero =>
    induction t with
    | lf b =>
      cases b
      · simp [BT.toBits]
      · simp only [BT.toBits, ite_true, Nat.testBit_two_pow_sub_one, decide_eq_false_iff_not]
        simp at hi ⊢; omega
    | nd l r ihl _ => simpa [BT.toBits] using ihl
  | succ d ih =>
    have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    cases t with
    | lf b =>
      cases b
      · simp [BT.toBits]
      · simp only [BT.toBits, ite_true, Nat.testBit_two_pow_sub_one, decide_eq_false_iff_not]
        omega
    | nd l r =>
      simp only [BT.toBits, Nat.testBit_or, Nat.testBit_shiftLeft, ih l i (by omega)]
      have hr := ih r (i - 2 ^ d) (by omega)
      simp [hr]

theorem BT.toBits_testBit (t : BT) (d i : Nat) (hi : i < 2 ^ d) :
    (t.toBits d).testBit i = t.get i d := by
  induction d generalizing t i with
  | zero =>
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    induction t with
    | lf b => cases b <;> simp [BT.toBits, BT.get]
    | nd l r ihl _ => simpa [BT.toBits, BT.get] using ihl
  | succ d ih =>
    have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    cases t with
    | lf b =>
      cases b
      · simp [BT.toBits, BT.get]
      · simp only [BT.toBits, BT.get, ite_true, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
        exact hi
    | nd l r =>
      by_cases hil : i < 2 ^ d
      · simp only [BT.toBits, Nat.testBit_or, Nat.testBit_shiftLeft, BT.get, hil, ite_true,
          ih l i hil]
        have : ¬ (2 ^ d <= i) := by omega
        simp [this]
      · simp only [BT.toBits, Nat.testBit_or, Nat.testBit_shiftLeft, BT.get, hil, ite_false,
          BT.toBits_testBit_high l d i (by omega), ih r (i - 2 ^ d) (by omega)]
        have : 2 ^ d <= i := by omega
        simp [this]

/-! ## Tree states on the wide window -/

theorem wideIndex_lt {p : Point} (hp : InWide p) : wideIndex p < 2 ^ 16 := by
  simp only [InWide] at hp
  simp only [wideIndex]
  have : (2 : Nat) ^ 16 = 65536 := by decide
  rw [this]
  omega

structure TreeState where
  tree : BT
  pos : Point
  dir : Direction

def treeBoard (t : BT) : Board :=
  fun p => if InWide p then t.get (wideIndex p) 16 else false

def TreeState.toState (s : TreeState) : State := ⟨treeBoard s.tree, s.pos, s.dir⟩

def TreeState.step (s : TreeState) : TreeState :=
  let d := turn (s.tree.get (wideIndex s.pos) 16) s.dir
  { tree := s.tree.flip (wideIndex s.pos) 16, pos := move s.pos d, dir := d }

theorem treeBoard_flip (t : BT) (p : Point) (hp : InWide p) :
    treeBoard (t.flip (wideIndex p) 16) = flip (treeBoard t) p := by
  funext q
  by_cases hq : InWide q
  · have heq : wideIndex p = wideIndex q ↔ q = p :=
      ⟨fun h => (wideIndex_injective hp hq h).symm, fun h => by rw [h]⟩
    simp only [treeBoard, hq, ite_true, flip]
    rw [BT.get_flip _ _ _ _ (wideIndex_lt hp) (wideIndex_lt hq)]
    by_cases h : q = p
    · subst h; simp
    · have hne : wideIndex p ≠ wideIndex q := fun e => h (heq.mp e)
      simp [hne, h]
  · have hne : q ≠ p := fun h => hq (h ▸ hp)
    simp [treeBoard, hq, flip, hne]

theorem TreeState.toState_step (s : TreeState) (hp : InWide s.pos) :
    s.step.toState = LangtonsAnt.step s.toState := by
  have hc : s.toState.board s.pos = s.tree.get (wideIndex s.pos) 16 := by
    simp [TreeState.toState, treeBoard, hp]
  simp only [TreeState.step, TreeState.toState, LangtonsAnt.step]
  rw [treeBoard_flip _ _ hp]
  change (⟨flip (treeBoard s.tree) s.pos, _, _⟩ : State) =
    ⟨flip s.toState.board s.pos, move s.toState.pos (turn (s.toState.board s.toState.pos) s.toState.dir),
      turn (s.toState.board s.toState.pos) s.toState.dir⟩
  rw [show s.toState.pos = s.pos from rfl, hc]
  rfl

theorem TreeState.toWide_toState (s : TreeState) :
    (⟨s.tree.toBits 16, s.pos, s.dir⟩ : WideState).toState = s.toState := by
  have hb : wideBoard (s.tree.toBits 16) = treeBoard s.tree := by
    funext p
    by_cases hp : InWide p
    · simp only [wideBoard, treeBoard, hp, ite_true]
      exact BT.toBits_testBit _ _ _ (wideIndex_lt hp)
    · simp [wideBoard, treeBoard, hp]
  simp only [WideState.toState, TreeState.toState, hb]

/-- Insert the black cells of a finite state into an all-white tree. -/
def treeOfCells : List Point -> BT
  | [] => .lf false
  | p :: ps => let t := treeOfCells ps
      if t.get (wideIndex p) 16 then t else t.flip (wideIndex p) 16

theorem treeOfCells_board (cells : List Point) (hbox : forall p, p ∈ cells -> InWide p) :
    treeBoard (treeOfCells cells) = fun p => decide (p ∈ cells) := by
  induction cells with
  | nil => funext q; simp [treeOfCells, treeBoard, BT.get]
  | cons p ps ih =>
    have hp := hbox p (by simp)
    have ht := ih (fun q hq => hbox q (by simp [hq]))
    funext q
    have hq0 := congrFun ht q
    by_cases hg : (treeOfCells ps).get (wideIndex p) 16 = true
    · have hpin : p ∈ ps := by
        have := congrFun ht p
        simp only [treeBoard, hp, ite_true, hg] at this
        exact of_decide_eq_true this.symm
      simp only [treeOfCells, hg, ite_true]
      rw [hq0]
      by_cases h : q = p <;> simp [h, hpin]
    · simp only [treeOfCells, hg]
      have hf := congrFun (treeBoard_flip (treeOfCells ps) p hp) q
      simp only [Bool.false_eq_true, ite_false] at hf ⊢
      rw [hf]
      simp only [flip, hq0]
      have hpnot : p ∉ ps := by
        intro hm
        apply hg
        have := congrFun ht p
        simp only [treeBoard, hp, ite_true] at this
        rw [this]
        simp [hm]
      by_cases h : q = p
      · subst h; simp [hpnot]
      · simp [h]

def FiniteState.toTree (s : FiniteState) : TreeState := ⟨treeOfCells s.black, s.pos, s.dir⟩

theorem FiniteState.toTree_toState (s : FiniteState) (hbox : forall p, p ∈ s.black -> InWide p) :
    s.toTree.toState = s.toState := by
  simp only [toTree, TreeState.toState, toState, treeOfCells_board s.black hbox]

/-- Run `n` steps inside the window, then check the half-plane entry on the bit encoding. -/
def checkTreeEntry (cut : Int) (target : FiniteState) : Nat -> TreeState -> Bool
  | 0, s => checkWideAgreement cut ⟨s.tree.toBits 16, s.pos, s.dir⟩ target
  | n + 1, s => decide (InWide s.pos) && checkTreeEntry cut target n s.step

theorem checkTreeEntry_sound {cut : Int} {target : FiniteState} {n : Nat} {s : TreeState}
    (h : checkTreeEntry cut target n s = true) :
    AgreesBelow cut (run s.toState n) target.toState := by
  induction n generalizing s with
  | zero =>
    have hh := checkWideAgreement_sound h
    rw [TreeState.toWide_toState] at hh
    exact hh
  | succ n ih =>
    simp only [checkTreeEntry, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh := ih h.2
    rw [TreeState.toState_step _ h.1] at hh
    change AgreesBelow cut (run (run s.toState 1) n) target.toState at hh
    rw [← run_add, Nat.add_comm 1 n] at hh
    exact hh

end LangtonsAnt
