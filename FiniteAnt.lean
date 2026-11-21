import LangtonsAnt

namespace LangtonsAnt

/-- A finite implementation whose interpretation is the original infinite board. -/
structure FiniteState where
  black : List Point
  pos : Point
  dir : Direction
  deriving Repr, DecidableEq

def FiniteState.toState (s : FiniteState) : State :=
  { board := fun p => decide (p ∈ s.black), pos := s.pos, dir := s.dir }

def toggleCells (cells : List Point) (p : Point) : List Point :=
  if p ∈ cells then cells.filter (fun q => q != p) else p :: cells

def FiniteState.step (s : FiniteState) : FiniteState :=
  let d := turn (decide (s.pos ∈ s.black)) s.dir
  { black := toggleCells s.black s.pos, pos := move s.pos d, dir := d }

def FiniteState.run (s : FiniteState) : Nat -> FiniteState
  | 0 => s
  | n + 1 => (s.run n).step

theorem toggleCells_board (cells : List Point) (p q : Point) :
    decide (q ∈ toggleCells cells p) = flip (fun r => decide (r ∈ cells)) p q := by
  by_cases hp : p ∈ cells <;> by_cases hq : q = p <;>
    simp [toggleCells, flip, hp, hq]

theorem FiniteState.toState_step (s : FiniteState) :
    s.step.toState = LangtonsAnt.step s.toState := by
  have hb : (fun q => decide (q ∈ toggleCells s.black s.pos)) =
      flip (fun q => decide (q ∈ s.black)) s.pos := by
    funext q
    exact toggleCells_board _ _ _
  unfold FiniteState.step toState LangtonsAnt.step
  simp only [hb]

theorem FiniteState.toState_run (s : FiniteState) (n : Nat) :
    (s.run n).toState = LangtonsAnt.run s.toState n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteState.run, toState_step, run_succ, ih]

theorem FiniteState.finiteSupport (s : FiniteState) : FiniteSupport s.toState.board := by
  refine ⟨s.black, ?_⟩
  intro p hp
  simpa [toState] using hp

def finiteBlank : FiniteState := ⟨[], (0, 0), .north⟩

@[simp] theorem finiteBlank_toState : finiteBlank.toState = blank := by
  rfl

end LangtonsAnt
