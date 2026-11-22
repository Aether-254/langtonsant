import RecordPair

/-!
# Unit-diagonal drift: the reduction shell

Ke's unit-diagonal exclusion says that a finite-support orbit which is eventually periodic (of any
positive period) never has a full one-period displacement in `{(1, -1), (-1, -1), (-1, 1), (1, 1)}`.
All of the analytic work is isolated in the single hypothesis `CoreUnitSE`: no consistent
(white-background) turn word has full displacement `(1, -1)`.

This file only *reduces* that core statement to the two headline theorems, using:

* `ConsistentWord.front_factor` (four consecutive right turns force all four headings to occur at
  some phase `a < P`, `ConsistentWord.exists_phase_dir`),
* `periodic_tail_consistent_at_start` (a periodic tail of a finite-support orbit yields a consistent
  read word at any start time) together with the fact that the drift of that word is the orbit drift
  rotated by the inverse of the starting heading,
* `ConsistentWord.realizable` (every consistent word is the read word of a finite-support orbit) for
  the word-level statement.

`CoreUnitSE` stays a hypothesis: this module adds no unproved constants, no placeholder proofs and
no trusted native evaluation, so the reduction is a pure kernel proof.
-/

namespace UnitDiagonal

open LangtonsAnt

/-- A full one-period displacement equal to one of `(1, -1)` and its quarter turns. -/
def UnitDiagonalDrift (v : Point) : Prop :=
  (v.1 = 1 ∨ v.1 = -1) ∧ (v.2 = 1 ∨ v.2 = -1)

/-- The core analytic statement, to be proved elsewhere: a consistent word never has full
displacement `(1, -1)`. -/
def CoreUnitSE : Prop :=
  forall (P : Nat) (w : Nat -> Bool), ConsistentWord P w -> wordDrift P w ≠ (1, -1)

/-! ## Rotations, turns and headings -/

/-- Turning right after turning left is the identity. -/
theorem direction_left_right (d : Direction) : d.left.right = d := by cases d <;> rfl

/-- A white cell turns the ant right. -/
theorem turn_false_right (d : Direction) : turn false d = d.right := rfl

/-- A black cell turns the ant left. -/
theorem turn_true_left (d : Direction) : turn true d = d.left := rfl

/-- One step of the turn word. -/
theorem wordTrace_succ (u : Nat -> Bool) (n : Nat) :
    (wordTrace u (n + 1)).2 = turn (u n) ((wordTrace u n).2) := rfl

/-- Every unit diagonal vector is a quarter turn of `(1, -1)`. -/
theorem exists_rotate_of_unitDiagonal {v : Point} (hv : UnitDiagonalDrift v) :
    exists r : Direction, rotatePoint r (1, -1) = v := by
  obtain ⟨h1, h2⟩ := hv
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ⟨.west, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩
  · exact ⟨.north, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩
  · exact ⟨.south, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩
  · exact ⟨.east, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩

/-! ## The heading of an orbit, read as a turn word from time `T` -/

/-- Reading the orbit from time `T` on as a turn word, the heading at time `T + n` is the rotation
of the word-trace heading at phase `n`, because the turn word always starts facing north. -/
theorem run_dir_wordTrace (s : State) (T : Nat) (n : Nat) :
    (run s (T + n)).dir =
      rotateDir (run s T).dir ((wordTrace (fun i => readColor s (T + i)) n).2) := by
  induction n with
  | zero =>
    have hzero : (wordTrace (fun i => readColor s (T + i)) 0).2 = .north := rfl
    rw [hzero, rotateDir_north, Nat.add_zero]
  | succ n ih =>
    have hT : T + (n + 1) = (T + n) + 1 := by omega
    rw [hT, run_succ]
    show turn (readColor s (T + n)) (run s (T + n)).dir =
      rotateDir (run s T).dir ((wordTrace (fun i => readColor s (T + i)) (n + 1)).2)
    rw [wordTrace_succ, rotateDir_turn, ih]

/-- The drift of the read word of a periodic tail, measured from its start, is the orbit drift
rotated by the inverse of the heading at that start. -/
theorem wordDrift_of_highway {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) :
    wordDrift P (fun i => readColor s (T + i)) =
      rotatePoint (inverseRotation (run s T).dir) v := by
  let t := run s T
  let u := normalize t.dir t.pos t
  have ht : HighwayFrom t 0 P v := by
    intro n _
    have hh := h (T + n) (by omega)
    simpa only [t, ← run_add, Nat.add_assoc] using hh
  have hu : HighwayFrom u 0 P (rotatePoint (inverseRotation t.dir) v) :=
    (ht.translate (negPoint t.pos)).rotate (inverseRotation t.dir)
  have hup : u.pos = (0, 0) := by
    have hz : addPoint (negPoint t.pos) t.pos = (0, 0) := by
      apply Prod.ext <;> simp only [addPoint, negPoint] <;> omega
    change rotatePoint (inverseRotation t.dir) (addPoint (negPoint t.pos) t.pos) = _
    rw [hz, rotatePoint_zero]
  have hud : u.dir = .north := by
    change rotateDir (inverseRotation t.dir) t.dir = .north
    have he := rotateDir_inverse t.dir .north
    simpa only [rotateDir_north] using he
  have hr : readColor u = fun i => readColor s (T + i) := by
    funext i
    rw [show readColor u i = readColor t i from normalize_readColor t.dir t.pos t i]
    simp only [t, readColor, run_add]
  rw [← hr]
  exact hu.word_drift hup hud

/-- A highway can be read from any later start time. -/
theorem highwayFrom_shift {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (a : Nat) : HighwayFrom s (T + a) P v :=
  fun n hn => h n (by omega)

/-! ## Every heading occurs among the phases of a consistent word -/

/-- A repeated word reads the same at a wrapped index. -/
theorem repeatWord_self_mod {P : Nat} (w : Nat -> Bool) (n : Nat) :
    repeatWord P w n = repeatWord P w (n % P) := by
  simp only [repeatWord, Nat.mod_mod]

/-- One period of a repeated word leaves the heading unchanged. -/
theorem repeatWord_dir_step {P : Nat} {w : Nat -> Bool} (hd : (wordTrace w P).2 = .north)
    (n : Nat) :
    (wordTrace (repeatWord P w) (n + P)).2 = (wordTrace (repeatWord P w) n).2 := by
  have h := repeatWord_trace_period hd n
  have h2 : wordTrace (repeatWord P w) (n + P) =
      (addPoint (wordDrift P w) (wordPos (repeatWord P w) n),
        (wordTrace (repeatWord P w) n).2) := h
  rw [h2]

/-- The direction of a repeated word is periodic in time. -/
theorem repeatWord_dir_period {P : Nat} {w : Nat -> Bool} (hd : (wordTrace w P).2 = .north)
    (n k : Nat) :
    (wordTrace (repeatWord P w) (n + P * k)).2 = (wordTrace (repeatWord P w) n).2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : n + P * (k + 1) = (n + P * k) + P := by rw [Nat.mul_succ]; omega
    rw [he, repeatWord_dir_step hd (n + P * k), ih]

/-- The direction only depends on the phase. -/
theorem repeatWord_dir_mod {P : Nat} {w : Nat -> Bool} (hd : (wordTrace w P).2 = .north)
    (m : Nat) :
    (wordTrace (repeatWord P w) m).2 = (wordTrace (repeatWord P w) (m % P)).2 := by
  have h := repeatWord_dir_period hd (m % P) (m / P)
  rw [Nat.mod_add_div] at h
  exact h

/-- Among four quarter turns, any direction shows up. -/
theorem dir_cover (e d : Direction) :
    e.left = d ∨ e = d ∨ e.right = d ∨ e.right.right = d := by
  cases e <;> cases d <;> simp [Direction.left, Direction.right]

/-- Every heading is taken at some phase below the period: four consecutive right turns cover all
four directions. -/
theorem ConsistentWord.exists_phase_dir {P : Nat} {w : Nat -> Bool} (h : ConsistentWord P w)
    (hP : 0 < P) (d : Direction) : exists a, a < P ∧ (wordTrace w a).2 = d := by
  have hrep : ConsistentWord P (repeatWord P w) :=
    ConsistentWord.congr h (fun j hj => (repeatWord_prefix w hj).symm)
  obtain ⟨i, _hi, h0, h1, h2, h3, _h4, _h5⟩ :=
    ConsistentWord.front_factor hrep hP
  have e1 : repeatWord P w (i + 1) = false := by
    rw [repeatWord_self_mod, h1]
  have e2 : repeatWord P w (i + 2) = false := by
    rw [repeatWord_self_mod, h2]
  have e3 : repeatWord P w (i + 3) = false := by
    rw [repeatWord_self_mod, h3]
  have t1 : (wordTrace (repeatWord P w) (i + 1)).2 = (wordTrace (repeatWord P w) i).2.left := by
    rw [wordTrace_succ, h0, turn_true_left]
  have t2 : (wordTrace (repeatWord P w) (i + 2)).2 = (wordTrace (repeatWord P w) i).2 := by
    rw [wordTrace_succ, e1, t1, turn_false_right, direction_left_right]
  have t3 : (wordTrace (repeatWord P w) (i + 3)).2 =
      (wordTrace (repeatWord P w) i).2.right := by
    rw [wordTrace_succ, e2, t2, turn_false_right]
  have t4 : (wordTrace (repeatWord P w) (i + 4)).2 =
      (wordTrace (repeatWord P w) i).2.right.right := by
    rw [wordTrace_succ, e3, t3, turn_false_right]
  have phase : forall j, (wordTrace (repeatWord P w) (i + j)).2 = d ->
      exists a, a < P ∧ (wordTrace w a).2 = d := by
    intro j hj
    refine ⟨(i + j) % P, Nat.mod_lt _ hP, ?_⟩
    have hmod : (wordTrace (repeatWord P w) (i + j)).2 =
        (wordTrace (repeatWord P w) ((i + j) % P)).2 := repeatWord_dir_mod h.1 (i + j)
    rw [← repeatWord_trace w (Nat.le_of_lt (Nat.mod_lt _ hP)), ← hmod]
    exact hj
  rcases dir_cover (wordTrace (repeatWord P w) i).2 d with hc | hc | hc | hc
  · exact phase 1 (t1.trans hc)
  · exact phase 2 (t2.trans hc)
  · exact phase 3 (t3.trans hc)
  · exact phase 4 (t4.trans hc)

/-! ## The two headline reductions -/

/-- Ke's unit-diagonal exclusion, orbit form: no finite-support orbit with a positive periodic tail
has a unit diagonal full displacement. -/
theorem no_unit_diagonal_periodic_tail (core : CoreUnitSE) {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (hv : UnitDiagonalDrift v) :
    ¬ HighwayFrom s T P v := by
  intro h
  obtain ⟨r, hr⟩ := exists_rotate_of_unitDiagonal hv
  have hc : ConsistentWord P (fun i => readColor s (T + i)) :=
    periodic_tail_consistent_at_start hs hP h
  obtain ⟨a, _ha, hphase⟩ :=
    ConsistentWord.exists_phase_dir hc hP (rotateDir (inverseRotation (run s T).dir) r)
  have horbit : (run s (T + a)).dir = r := by
    rw [run_dir_wordTrace s T a, hphase, inverse_rotateDir]
  have hshift := highwayFrom_shift h a
  have hdrift : wordDrift P (fun i => readColor s (T + a + i)) = (1, -1) := by
    have hd := wordDrift_of_highway hshift
    rw [horbit, ← hr, rotatePoint_inverse] at hd
    exact hd
  have hc' : ConsistentWord P (fun i => readColor s (T + a + i)) :=
    periodic_tail_consistent_at_start hs hP hshift
  exact core P _ hc' hdrift

/-- Ke's unit-diagonal exclusion, word form: a consistent word never has a unit diagonal full
displacement. -/
theorem consistentWord_not_unitDiagonal (core : CoreUnitSE) {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) : ¬ UnitDiagonalDrift (wordDrift P w) := by
  intro hv
  have hP : 0 < P := by
    rcases Nat.eq_zero_or_pos P with hzero | hpos
    · exact absurd (by rw [hzero]; rfl : wordDrift P w = (0, 0)) h.2.1
    · exact hpos
  obtain ⟨s, hs, hh, _⟩ := ConsistentWord.realizable h hP
  exact no_unit_diagonal_periodic_tail core hs hP hv hh

end UnitDiagonal
