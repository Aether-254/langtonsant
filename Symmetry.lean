import Highway

namespace LangtonsAnt

/-- The parameter names the image of north under the rotation. -/
def rotatePoint : Direction -> Point -> Point
  | .north, p => p
  | .east, p => (p.2, -p.1)
  | .south, p => (-p.1, -p.2)
  | .west, p => (-p.2, p.1)

def rotateDir : Direction -> Direction -> Direction
  | .north, d => d
  | .east, d => d.right
  | .south, d => d.right.right
  | .west, d => d.left

def inverseRotation : Direction -> Direction
  | .north => .north
  | .east => .west
  | .south => .south
  | .west => .east

def negPoint (p : Point) : Point := (-p.1, -p.2)

@[simp] theorem rotatePoint_inverse (r : Direction) (p : Point) :
    rotatePoint (inverseRotation r) (rotatePoint r p) = p := by
  cases r <;> cases p <;> simp [rotatePoint, inverseRotation]

@[simp] theorem inverse_rotatePoint (r : Direction) (p : Point) :
    rotatePoint r (rotatePoint (inverseRotation r) p) = p := by
  cases r <;> cases p <;> simp [rotatePoint, inverseRotation]

@[simp] theorem rotateDir_inverse (r d : Direction) :
    rotateDir (inverseRotation r) (rotateDir r d) = d := by
  cases r <;> cases d <;> rfl

@[simp] theorem inverse_rotateDir (r d : Direction) :
    rotateDir r (rotateDir (inverseRotation r) d) = d := by
  cases r <;> cases d <;> rfl

@[simp] theorem rotateDir_north (r : Direction) : rotateDir r .north = r := by
  cases r <;> rfl

@[simp] theorem rotatePoint_zero (r : Direction) : rotatePoint r (0, 0) = (0, 0) := by
  cases r <;> rfl

theorem rotatePoint_add (r : Direction) (p q : Point) :
    rotatePoint r (addPoint p q) = addPoint (rotatePoint r p) (rotatePoint r q) := by
  cases r <;> apply Prod.ext <;> simp [rotatePoint, addPoint] <;> omega

theorem rotatePoint_move (r d : Direction) (p : Point) :
    rotatePoint r (move p d) = move (rotatePoint r p) (rotateDir r d) := by
  cases r <;> cases d <;>
    apply Prod.ext <;> simp [rotatePoint, rotateDir, move, Direction.right, Direction.left] <;>
    omega

theorem rotateDir_turn (r d : Direction) (c : Bool) :
    rotateDir r (turn c d) = turn c (rotateDir r d) := by
  cases r <;> cases d <;> cases c <;> rfl

def rotateState (r : Direction) (s : State) : State :=
  { board := fun p => s.board (rotatePoint (inverseRotation r) p)
    pos := rotatePoint r s.pos
    dir := rotateDir r s.dir }

@[simp] theorem rotateState_inverse (r : Direction) (s : State) :
    rotateState (inverseRotation r) (rotateState r s) = s := by
  have hi : inverseRotation (inverseRotation r) = r := by cases r <;> rfl
  cases s
  simp [rotateState, hi]

@[simp] theorem inverse_rotateState (r : Direction) (s : State) :
    rotateState r (rotateState (inverseRotation r) s) = s := by
  have hi : inverseRotation (inverseRotation r) = r := by cases r <;> rfl
  cases s
  simp [rotateState, hi]

theorem rotate_step (r : Direction) (s : State) :
    step (rotateState r s) = rotateState r (step s) := by
  have hf : flip (fun p => s.board (rotatePoint (inverseRotation r) p)) (rotatePoint r s.pos) =
      fun p => flip s.board s.pos (rotatePoint (inverseRotation r) p) := by
    funext p
    have heq : p = rotatePoint r s.pos ↔ rotatePoint (inverseRotation r) p = s.pos := by
      constructor
      · intro h; simp [h]
      · intro h
        rw [← h, inverse_rotatePoint]
    simp [flip, heq]
  simp only [step, rotateState, rotatePoint_inverse, hf, rotateDir_turn, rotatePoint_move]

theorem rotate_run (r : Direction) (s : State) (n : Nat) :
    run (rotateState r s) n = rotateState r (run s n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run_succ, ih, rotate_step]

theorem rotate_readColor (r : Direction) (s : State) (n : Nat) :
    readColor (rotateState r s) n = readColor s n := by
  unfold readColor
  rw [rotate_run]
  simp only [rotateState, rotatePoint_inverse]

theorem HighwayFrom.rotate {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (r : Direction) :
    HighwayFrom (rotateState r s) T P (rotatePoint r v) := by
  intro n hn
  have hh := h n hn
  rw [rotate_run, rotate_run]
  simp only [rotateState]
  constructor
  · change rotatePoint r (run s (n + P)).pos = addPoint _ _
    rw [hh.1]
    exact rotatePoint_add r _ _
  · exact congrArg (rotateDir r) hh.2

theorem HighwayFrom.translate {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (origin : Point) :
    HighwayFrom (LangtonsAnt.translate origin s) T P v := by
  intro n hn
  have hh := h n hn
  rw [translate_run, translate_run]
  simp only [LangtonsAnt.translate]
  constructor
  · rw [hh.1]
    apply Prod.ext <;> simp [addPoint] <;> omega
  · exact hh.2

theorem StandardHighwayFrom.rotate {s : State} {T : Nat} {v : Point}
    (h : StandardHighwayFrom s T v) (r : Direction) :
    StandardHighwayFrom (rotateState r s) T (rotatePoint r v) :=
  ⟨h.1.rotate r, fun n => (rotate_readColor r s _).trans (h.2 n)⟩

theorem StandardHighwayFrom.translate {s : State} {T : Nat} {v : Point}
    (h : StandardHighwayFrom s T v) (origin : Point) :
    StandardHighwayFrom (LangtonsAnt.translate origin s) T v :=
  ⟨h.1.translate origin, fun n => (translate_readColor origin s _).trans (h.2 n)⟩

theorem finiteSupport_translate {s : State} (h : FiniteSupport s.board) (v : Point) :
    FiniteSupport (translate v s).board := by
  obtain ⟨cells, hc⟩ := h
  refine ⟨cells.map (addPoint v), ?_⟩
  intro p hp
  exact List.mem_map.mpr ⟨subPoint p v, hc _ hp, addPoint_subPoint v p⟩

theorem finiteSupport_rotate {s : State} (h : FiniteSupport s.board) (r : Direction) :
    FiniteSupport (rotateState r s).board := by
  obtain ⟨cells, hc⟩ := h
  refine ⟨cells.map (rotatePoint r), ?_⟩
  intro p hp
  exact List.mem_map.mpr ⟨rotatePoint (inverseRotation r) p, hc _ hp, inverse_rotatePoint r p⟩

def pose (r : Direction) (origin : Point) (s : State) : State :=
  translate origin (rotateState r s)

def normalize (r : Direction) (origin : Point) (s : State) : State :=
  rotateState (inverseRotation r) (translate (negPoint origin) s)

@[simp] theorem pose_normalize (r : Direction) (origin : Point) (s : State) :
    pose r origin (normalize r origin s) = s := by
  simp only [pose, normalize, inverse_rotateState, translate_add]
  have hz : addPoint origin (negPoint origin) = (0, 0) := by
    apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
  rw [hz, translate_zero]

@[simp] theorem normalize_pose (r : Direction) (origin : Point) (s : State) :
    normalize r origin (pose r origin s) = s := by
  simp only [pose, normalize, translate_add]
  have hz : addPoint (negPoint origin) origin = (0, 0) := by
    apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
  rw [hz, translate_zero, rotateState_inverse]

theorem pose_run (r : Direction) (origin : Point) (s : State) (n : Nat) :
    run (pose r origin s) n = pose r origin (run s n) := by
  simp only [pose, translate_run, rotate_run]

theorem normalize_run (r : Direction) (origin : Point) (s : State) (n : Nat) :
    run (normalize r origin s) n = normalize r origin (run s n) := by
  simp only [normalize, translate_run, rotate_run]

theorem normalize_readColor (r : Direction) (origin : Point) (s : State) (n : Nat) :
    readColor (normalize r origin s) n = readColor s n := by
  simp only [normalize, rotate_readColor, translate_readColor]

theorem finiteSupport_normalize {s : State} (h : FiniteSupport s.board)
    (r : Direction) (origin : Point) : FiniteSupport (normalize r origin s).board :=
  finiteSupport_rotate (finiteSupport_translate h _) _

theorem diagonal_rotated_southwest (r : Direction) : DiagonalDrift (rotatePoint r (-2, -2)) := by
  cases r <;> simp [DiagonalDrift, rotatePoint]

end LangtonsAnt
