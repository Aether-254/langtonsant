import Std
import Lean.Elab.Tactic.Omega

/-!
Classical Langton ant on the infinite square grid: white turns right,
black turns left, then the current cell is flipped and the ant moves.

The highway conjecture is stated as a proposition, not assumed as an axiom.
The proved escape theorem is strictly weaker than eventual highway entry.
-/

namespace LangtonsAnt

abbrev Point := Int × Int
abbrev Board := Point -> Bool

inductive Direction where
  | north | east | south | west
  deriving DecidableEq, Repr

def Direction.right : Direction -> Direction
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north

def Direction.left : Direction -> Direction
  | .north => .west
  | .east => .north
  | .south => .east
  | .west => .south

def Direction.horizontal : Direction -> Bool
  | .east | .west => true
  | .north | .south => false

def turn (black : Bool) (d : Direction) : Direction :=
  if black then d.left else d.right

def move (p : Point) : Direction -> Point
  | .north => (p.1, p.2 + 1)
  | .east => (p.1 + 1, p.2)
  | .south => (p.1, p.2 - 1)
  | .west => (p.1 - 1, p.2)

def flip (board : Board) (p : Point) : Board :=
  fun q => if q = p then !(board q) else board q

structure State where
  board : Board
  pos : Point
  dir : Direction

def step (s : State) : State :=
  let d := turn (s.board s.pos) s.dir
  { board := flip s.board s.pos, pos := move s.pos d, dir := d }

def run (s : State) : Nat -> State
  | 0 => s
  | n + 1 => step (run s n)

@[simp] theorem run_zero (s : State) : run s 0 = s := rfl
@[simp] theorem run_succ (s : State) (n : Nat) :
    run s (n + 1) = step (run s n) := rfl

theorem run_add (s : State) (m n : Nat) :
    run s (m + n) = run (run s m) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.add_succ, run_succ, ih]

@[simp] theorem flip_same (board : Board) (p : Point) :
    flip board p p = !(board p) := by simp [flip]

@[simp] theorem flip_other (board : Board) {p q : Point} (h : q ≠ p) :
    flip board p q = board q := by simp [flip, h]

@[simp] theorem flip_twice (board : Board) (p : Point) :
    flip (flip board p) p = board := by
  funext q
  by_cases h : q = p <;> simp [flip, h]

def FiniteSupport (board : Board) : Prop :=
  exists cells : List Point, forall p, board p = true -> p ∈ cells

theorem finiteSupport_flip {board : Board} (h : FiniteSupport board) (p : Point) :
    FiniteSupport (flip board p) := by
  obtain ⟨cells, hc⟩ := h
  refine ⟨p :: cells, ?_⟩
  intro q hq
  by_cases heq : q = p
  · simp [heq]
  · exact List.mem_cons_of_mem p (hc q (by simpa [flip, heq] using hq))

theorem finiteSupport_run (s : State) (h : FiniteSupport s.board) (n : Nat) :
    FiniteSupport (run s n).board := by
  induction n with
  | zero => exact h
  | succ n ih => exact finiteSupport_flip ih (run s n).pos

def weight (p : Point) : Int := p.1 + p.2

def axisParity (s : State) : Int :=
  (weight s.pos + if s.dir.horizontal then 1 else 0) % 2

theorem axisParity_step (s : State) : axisParity (step s) = axisParity s := by
  obtain ⟨board, pos, dir⟩ := s
  cases dir <;> cases hb : board pos <;>
    simp [axisParity, step, turn, move, weight, Direction.horizontal,
      Direction.left, Direction.right, hb] <;> omega

theorem axisParity_run (s : State) (n : Nat) :
    axisParity (run s n) = axisParity s := by
  induction n with
  | zero => rfl
  | succ n ih => exact (axisParity_step _).trans ih

theorem same_cell_same_axis (s : State) {m n : Nat}
    (h : (run s m).pos = (run s n).pos) :
    (run s m).dir.horizontal = (run s n).dir.horizontal := by
  have hp := (axisParity_run s m).trans (axisParity_run s n).symm
  unfold axisParity at hp
  rw [h] at hp
  cases hm : (run s m).dir.horizontal <;>
    cases hn : (run s n).dir.horizontal <;> simp_all <;> omega

/- At an extremal northeast corner, the entry axis fixes the only allowed color. -/
theorem corner_color {p q : Point} {d : Direction} {black : Bool}
    (hmove : move p d = q) (hin : weight p <= weight q)
    (hout : weight (move q (turn black d)) <= weight q) :
    black = !d.horizontal := by
  subst q
  cases d <;> cases black <;>
    simp_all [move, turn, Direction.left, Direction.right, Direction.horizontal, weight] <;>
    omega

def Recurrent (f : Nat -> Point) (p : Point) : Prop :=
  forall N, exists n, N <= n ∧ f n = p

/- A finite range has a tail containing only infinitely recurring values. -/
theorem recurrent_tail (f : Nat -> Point) (cells : List Point) :
    exists N, forall n, N <= n -> f n ∈ cells -> Recurrent f (f n) := by
  classical
  induction cells with
  | nil => exact ⟨0, by simp⟩
  | cons p cells ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hp : Recurrent f p
    · refine ⟨N, ?_⟩
      intro n hn hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · simpa [heq] using hp
      · exact hN n hn hmem
    · simp only [Recurrent, Classical.not_forall, not_exists, not_and] at hp
      obtain ⟨M, hM⟩ := hp
      refine ⟨N + M, ?_⟩
      intro n hn hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · exact False.elim (hM n (by omega) heq)
      · exact hN n (by omega) hmem

theorem finite_range_recurrent_max (f : Nat -> Point) (cells : List Point)
    (hcells : forall n, f n ∈ cells) :
    exists T p, Recurrent f p ∧ forall n, T <= n -> weight (f n) <= weight p := by
  classical
  obtain ⟨T, hT⟩ := recurrent_tail f cells
  let recurring := cells.filter (fun p => decide (Recurrent f p))
  have hmem : f T ∈ recurring := by
    simp [recurring, hcells T, hT T (by omega) (hcells T)]
  have hnonempty : recurring.map weight ≠ [] :=
    List.ne_nil_of_mem (List.mem_map.mpr ⟨f T, hmem, rfl⟩)
  obtain ⟨p, hp, hpmax⟩ := List.mem_map.mp (List.max_mem hnonempty)
  have hrec : Recurrent f p := by
    simpa [recurring] using (List.mem_filter.mp hp).2
  refine ⟨T, p, hrec, ?_⟩
  intro n hn
  have hmemn : f n ∈ recurring := by
    simp [recurring, hcells n, hT n hn (hcells n)]
  have hle : weight (f n) <= (recurring.map weight).max hnonempty :=
    List.le_max_of_mem (List.mem_map.mpr ⟨f n, hmemn, rfl⟩)
  simpa [hpmax] using hle

/- Repeated visits flip a cell, so its observed color cannot eventually be constant. -/
theorem recurrent_not_fixed_color (s : State) (p : Point)
    (hrec : Recurrent (fun n => (run s n).pos) p) (T : Nat) (color : Bool) :
    ¬(forall n, T <= n -> (run s n).pos = p -> (run s n).board p = color) := by
  intro hfixed
  obtain ⟨m, hm, hpos⟩ := hrec T
  have hstart : (run s (m + 1)).board p = !color := by
    simp [run, step, flip, hpos, hfixed m hm hpos]
  have hpersist : forall k, (run s (m + 1 + k)).board p = !color := by
    intro k
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
      have haway : (run s (m + 1 + k)).pos ≠ p := by
        intro heq
        have hc := hfixed (m + 1 + k) (by omega) heq
        cases color <;> simp_all
      rw [show m + 1 + (k + 1) = (m + 1 + k) + 1 by omega, run_succ]
      change flip (run s (m + 1 + k)).board (run s (m + 1 + k)).pos p = !color
      rw [flip_other _ (Ne.symm haway)]
      exact ih
  obtain ⟨n, hn, hnpos⟩ := hrec (m + 1)
  have hp := hpersist (n - (m + 1))
  have heq : m + 1 + (n - (m + 1)) = n := by omega
  rw [heq] at hp
  have hc := hfixed n (by omega) hnpos
  cases color <;> simp_all

/-- No trajectory is confined to a finite list of cells, even for an infinite initial board. -/
theorem escapes_finite_set (s : State) (cells : List Point) :
    exists n, (run s n).pos ∉ cells := by
  classical
  apply Classical.byContradiction
  intro h
  have hcells : forall n, (run s n).pos ∈ cells := by simpa using h
  obtain ⟨T, p, hrec, hbound⟩ :=
    finite_range_recurrent_max (fun n => (run s n).pos) cells hcells
  obtain ⟨m, hm, hmpos⟩ := hrec (T + 1)
  apply recurrent_not_fixed_color s p hrec (T + 1) (!(run s m).dir.horizontal)
  intro n hn hnpos
  cases n with
  | zero => omega
  | succ k =>
    have hin := hbound k (by omega)
    have hout := hbound (k + 1 + 1) (by omega)
    have hmove : move (run s k).pos (run s (k + 1)).dir = p := by
      simpa only [run_succ, step] using hnpos
    have hnext : (run s (k + 1 + 1)).pos =
        move p (turn ((run s (k + 1)).board p) (run s (k + 1)).dir) := by
      simp only [run_succ, step] at hnpos ⊢
      rw [hnpos]
    rw [hnext] at hout
    have hcolor := corner_color hmove hin hout
    have haxis := same_cell_same_axis s (hnpos.trans hmpos.symm)
    exact hcolor.trans (congrArg Bool.not haxis)

/-- Escape is possible after every time bound; this does not assert permanent departure. -/
theorem escapes_finite_set_after (s : State) (cells : List Point) (T : Nat) :
    exists n, T <= n ∧ (run s n).pos ∉ cells := by
  obtain ⟨k, hk⟩ := escapes_finite_set (run s T) cells
  refine ⟨T + k, by omega, ?_⟩
  simpa only [run_add] using hk

def HighwayFrom (s : State) (T period : Nat) (drift : Point) : Prop :=
  forall n, T <= n ->
    (run s (n + period)).pos =
      ((run s n).pos.1 + drift.1, (run s n).pos.2 + drift.2) ∧
    (run s (n + period)).dir = (run s n).dir

def DiagonalDrift (v : Point) : Prop :=
  (v.1 = 2 ∨ v.1 = -2) ∧ (v.2 = 2 ∨ v.2 = -2)

/-- An unresolved necessary target for the classical, standard-highway conjecture. -/
def Period104Conjecture : Prop :=
  forall s : State, FiniteSupport s.board ->
    exists T v, DiagonalDrift v ∧ HighwayFrom s T 104 v

def blank : State :=
  { board := fun _ => false, pos := (0, 0), dir := .north }

def readColor (s : State) (n : Nat) : Bool :=
  (run s n).board (run s n).pos

/-- A finite reference block, chosen after the known blank-orbit transient.
This definition by itself does not prove that the blank orbit repeats forever. -/
def standardColor (phase : Nat) : Bool :=
  readColor blank (10000 + phase % 104)

def StandardHighwayFrom (s : State) (T : Nat) (drift : Point) : Prop :=
  HighwayFrom s T 104 drift ∧
  forall k, readColor s (T + k) = standardColor k

/-- The open problem. The existential start time also chooses the cyclic phase.
Matching reads fixes the turn word; the initial heading allows a quarter-turn rotation. -/
def HighwayConjecture : Prop :=
  forall s : State, FiniteSupport s.board ->
    exists T v, DiagonalDrift v ∧ StandardHighwayFrom s T v

theorem highwayConjecture_implies_period104 (h : HighwayConjecture) :
    Period104Conjecture := by
  intro s hs
  obtain ⟨T, v, hv, htrace, _⟩ := h s hs
  exact ⟨T, v, hv, htrace⟩

end LangtonsAnt
