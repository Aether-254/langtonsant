import BoundedMemory

/-!
# Full-state time reversal of Langton's ant, and its axis-parity obstruction

This module formalizes the exact time reversal `reverseC` of a complete ant state
`(B, p, d)`, namely `(B Δ {p}, p, opp (turn (B p) d))`. It proves that this map is an
involution (`reverseC_involutive`), that it conjugates one forward step into one backward
step (`step_reverseC_step`), that it preserves finite board support
(`reverseC_finiteSupport`), and hence that running `k` steps of the reversal undoes the last
`k` steps of any finite run (`run_reverseC_run`), so that the reversed run reads exactly the
complemented colors in reverse order (`read_reverseC_run`). It then proves the obstruction
used by the periodic-tail campaign: `axisParity` is invariant along a run
(`axisParity_run`), while `reverseC` always flips it (`reverseC_axis_ne`) and even-board
translations preserve it (`translate_even_axis_C`), so no state of a run equals the exact
reversal of any of its own states (`run_ne_reverseC_run`), nor an even-board translate of
one (`run_ne_translate_reverseC_run`), nor even such a translate with merely matching pose
(`run_pose_ne_translate_reverseC_C`).

Provenance: research/persist-C-periodic-tail-2026-11-23.md, session 2, written by
GPT-6 Astra. The session-2 material is integrated unchanged apart from wrapping the
declarations in the namespace `LangtonsAnt.TimeReversal` and deleting the scratch file's
trailing diagnostic lines; every definition and proof is verbatim.
-/

-- Integration note: the required build flags turn linter warnings into errors. The scratch
-- file was kernel-checked without warnings-as-errors, so the unused-`simp`-argument linter
-- (which fires inside the `cases ... <;> simp [...] <;> omega` scripts below) is disabled
-- here. No definition or proof is otherwise touched.
set_option linter.unusedSimpArgs false

namespace LangtonsAnt.TimeReversal

def oppositeC : Direction → Direction
  | .north => .south
  | .east => .west
  | .south => .north
  | .west => .east

theorem oppositeC_twice (d : Direction) : oppositeC (oppositeC d) = d := by
  cases d <;> rfl

theorem move_oppositeC (p : Point) (d : Direction) :
    move (move p d) (oppositeC d) = p := by
  cases d <;> simp [move, oppositeC]

theorem reversal_turn_C (b : Bool) (d : Direction) :
    turn (!b) (oppositeC (turn b d)) = oppositeC d := by
  cases b <;> cases d <;> rfl

def reverseC (s : State) : State :=
  { board := flip s.board s.pos
    pos := s.pos
    dir := oppositeC (turn (s.board s.pos) s.dir) }

theorem reverseC_involutive (s : State) : reverseC (reverseC s) = s := by
  simp only [reverseC, flip_same, flip_twice, reversal_turn_C, oppositeC_twice]

theorem step_reverseC (s : State) :
    step (reverseC s) =
      { board := s.board, pos := move s.pos (oppositeC s.dir), dir := oppositeC s.dir } := by
  simp only [step, reverseC, flip_same, flip_twice, reversal_turn_C]

theorem step_reverseC_step (s : State) : step (reverseC (step s)) = reverseC s := by
  rw [step_reverseC]
  simp only [step, move_oppositeC, reverseC]

theorem reverseC_finiteSupport {s : State} (hs : FiniteSupport s.board) :
    FiniteSupport (reverseC s).board :=
  finiteSupport_flip hs s.pos

theorem run_reverseC_run (s : State) (n k : Nat) :
    run (reverseC (run s (n + k))) k = reverseC (run s n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, run_succ s (n + k)]
      rw [show k + 1 = 1 + k by omega, run_add]
      simp only [run_succ, run_zero, step_reverseC_step]
      exact ih

theorem read_reverseC_run (s : State) (n k : Nat) :
    readColor (reverseC (run s (n + k))) k = !(readColor s n) := by
  unfold readColor
  rw [run_reverseC_run]
  exact flip_same _ _

theorem reverseC_axis_ne (s : State) : axisParity (reverseC s) ≠ axisParity s := by
  obtain ⟨board, pos, dir⟩ := s
  cases dir <;> cases hb : board pos <;>
    simp [axisParity, reverseC, turn, oppositeC, Direction.horizontal,
      Direction.left, Direction.right, hb] <;> omega

theorem run_ne_reverseC_run (s : State) (n m : Nat) :
    run s n ≠ reverseC (run s m) := by
  intro he
  have ha := axisParity_run s n
  rw [he] at ha
  exact reverseC_axis_ne (run s m) (ha.trans (axisParity_run s m).symm)

theorem translate_even_axis_C (u : Point) (s : State) (hu : weight u % 2 = 0) :
    axisParity (translate u s) = axisParity s := by
  obtain ⟨board, pos, dir⟩ := s
  cases dir <;> simp [axisParity, translate, addPoint, weight, Direction.horizontal] at * <;>
    omega

theorem run_ne_translate_reverseC_run (s : State) (n m : Nat) (u : Point)
    (hu : weight u % 2 = 0) : run s n ≠ translate u (reverseC (run s m)) := by
  intro he
  have ha := axisParity_run s n
  rw [he, translate_even_axis_C u _ hu] at ha
  exact reverseC_axis_ne (run s m) (ha.trans (axisParity_run s m).symm)

theorem run_pose_ne_translate_reverseC_C (s : State) (n m : Nat) (u : Point)
    (hu : weight u % 2 = 0) :
    ¬((run s n).pos = addPoint u (run s m).pos ∧
      (run s n).dir = (reverseC (run s m)).dir) := by
  rintro ⟨hp, hd⟩
  have hpose : axisParity (run s n) = axisParity (translate u (reverseC (run s m))) := by
    simp only [axisParity, translate, reverseC] at hp hd ⊢
    rw [hp, hd]
    rfl
  rw [translate_even_axis_C u _ hu] at hpose
  have ha := axisParity_run s n
  exact reverseC_axis_ne (run s m)
    (hpose.symm.trans (ha.trans (axisParity_run s m).symm))

end LangtonsAnt.TimeReversal
