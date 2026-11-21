import VariableRecoveryBounds

namespace LangtonsAnt

theorem turn_direction_injective (c : Bool) (d e : Direction) (h : turn c d = turn c e) : d = e := by
  cases c <;> cases d <;> cases e <;> simp_all [turn, Direction.left, Direction.right]

theorem move_point_injective (d : Direction) (p q : Point) (h : move p d = move q d) : p = q := by
  cases d <;> apply Prod.ext <;> simp only [move, Prod.mk.injEq] at h ⊢ <;> omega

/-- Equal current reads extend an already established highway backward by one step. -/
theorem HighwayFrom.extend_one {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s (T + 1) P v) (hc : readColor s (T + P) = readColor s T) :
    HighwayFrom s T P v := by
  intro n hn
  by_cases hl : T + 1 <= n
  · exact h n hl
  · have he : n = T := by omega
    subst n
    obtain ⟨hp, hd⟩ := h (T + 1) (Nat.le_refl _)
    rw [show T + 1 + P = (T + P) + 1 by omega] at hp hd
    change turn (readColor s (T + P)) (run s (T + P)).dir =
      turn (readColor s T) (run s T).dir at hd
    rw [hc] at hd
    have hd0 := turn_direction_injective _ _ _ hd
    change move (run s (T + P)).pos (turn (readColor s (T + P)) (run s (T + P)).dir) =
      ((move (run s T).pos (turn (readColor s T) (run s T).dir)).1 + v.1,
        (move (run s T).pos (turn (readColor s T) (run s T).dir)).2 + v.2) at hp
    rw [hc, hd0] at hp
    have hm : move (run s (T + P)).pos (turn (readColor s T) (run s T).dir) =
        move (addPoint v (run s T).pos) (turn (readColor s T) (run s T).dir) := by
      rw [move_addPoint]
      simpa only [addPoint, Int.add_comm] using hp
    refine ⟨?_, hd0⟩
    simpa only [addPoint, Int.add_comm] using move_point_injective _ _ _ hm

theorem HighwayFrom.extend_prefix {s : State} {T P : Nat} {v : Point} (k : Nat)
    (h : HighwayFrom s (T + k) P v)
    (hc : forall n, T <= n -> n < T + k -> readColor s (n + P) = readColor s n) :
    HighwayFrom s T P v := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
    have he : HighwayFrom s (T + k) P v :=
      HighwayFrom.extend_one (T := T + k) h (hc (T + k) (by omega) (by omega))
    exact ih he (fun n hn hl => hc n hn (by omega))

/-- Read trace of one collision followed forever by the certified standard word. -/
def recoveryColor (j : Nat) : Bool :=
  if j < 548 then obstacleColor j else certifiedColor (j - 548)

def recoveryColorBits (j : Nat) : Bool :=
  if j < 548 then collisionWordBits.testBit j else standardWordBits.testBit ((j - 548) % 104)

theorem recoveryColor_eq_bits (j : Nat) : recoveryColor j = recoveryColorBits j := by
  by_cases hj : j < 548
  · simp only [recoveryColor, recoveryColorBits, hj, ite_true, obstacleColor_bits, Nat.mod_eq_of_lt hj]
  · simp only [recoveryColor, recoveryColorBits, hj, ite_false, certifiedColor_bits]

set_option maxRecDepth 100000 in
theorem recoveryColor_boundary_check :
    recoveryColorBits (418 + 104) ≠ recoveryColorBits 418 ∧
      (forall j : Fin 129, recoveryColorBits (419 + j.val + 104) = recoveryColorBits (419 + j.val)) := by
  decide +kernel

theorem finiteSchedule_last_collision_reads (f : Nat -> Nat) (n j : Nat) :
    readColor (variableObstacles (schedulePrefix f n)) (12496 + scheduleTime f n + j) = recoveryColor j := by
  by_cases hj : j < 548
  · rw [recoveryColor, ite_eq_left hj]
    exact finiteSchedule_collision_reads f n n (Nat.le_refl _) j hj
  · have ht : 12496 + scheduleTime f n + j = 13044 + scheduleTime f n + (j - 548) := by omega
    rw [recoveryColor, ite_eq_right hj, ht, (finiteSchedule_standard f n).2, standardColor_eq_certifiedColor]

theorem finiteSchedule_exact_highway (f : Nat -> Nat) (n : Nat) :
    HighwayFrom (variableObstacles (schedulePrefix f n)) (12915 + scheduleTime f n) 104 (-2, -2) := by
  apply HighwayFrom.extend_prefix 129
  · have ht : 12915 + scheduleTime f n + 129 = 13044 + scheduleTime f n := by omega
    rw [ht]
    exact (finiteSchedule_standard f n).1
  · intro t ht hl
    let j := t - (12915 + scheduleTime f n)
    have hj : j < 129 := by dsimp [j]; omega
    have he : t = 12496 + scheduleTime f n + (419 + j) := by dsimp [j]; omega
    rw [he, Nat.add_assoc, finiteSchedule_last_collision_reads, finiteSchedule_last_collision_reads,
      recoveryColor_eq_bits, recoveryColor_eq_bits]
    exact recoveryColor_boundary_check.2 ⟨j, hj⟩

theorem finiteSchedule_exact_start_lower_bound (f : Nat -> Nat) (n T : Nat) (v : Point)
    (h : HighwayFrom (variableObstacles (schedulePrefix f n)) T 104 v) :
    12915 + scheduleTime f n <= T := by
  by_cases ht : 12915 + scheduleTime f n <= T
  · exact ht
  · have hh := h.reads_periodic (n := 12496 + scheduleTime f n + 418) (by omega)
    rw [Nat.add_assoc, finiteSchedule_last_collision_reads, finiteSchedule_last_collision_reads,
      recoveryColor_eq_bits, recoveryColor_eq_bits] at hh
    exact False.elim (recoveryColor_boundary_check.1 hh)

/-- Exact onset of the permanent geometric 104-step highway, allowing any phase and drift. -/
theorem finiteSchedule_exact_highway_start (f : Nat -> Nat) (n : Nat) :
    HighwayFrom (variableObstacles (schedulePrefix f n)) (12915 + scheduleTime f n) 104 (-2, -2) ∧
      forall T v, HighwayFrom (variableObstacles (schedulePrefix f n)) T 104 v ->
        12915 + scheduleTime f n <= T :=
  ⟨finiteSchedule_exact_highway f n, finiteSchedule_exact_start_lower_bound f n⟩

set_option maxRecDepth 100000 in
theorem recoveryColor_aligned_check :
    forall j : Fin 104, recoveryColorBits (444 + j.val) = standardWordBits.testBit j.val := by
  decide +kernel

/-- A phase-aligned standard certificate starts 25 steps after the exact geometric onset. -/
theorem finiteSchedule_earlier_standard (f : Nat -> Nat) (n : Nat) :
    StandardHighwayFrom (variableObstacles (schedulePrefix f n)) (12940 + scheduleTime f n) (-2, -2) := by
  constructor
  · intro t ht
    exact finiteSchedule_exact_highway f n t (by omega)
  · intro j
    rw [standardColor_eq_certifiedColor]
    by_cases hj : j < 104
    · rw [show 12940 + scheduleTime f n + j = 12496 + scheduleTime f n + (444 + j) by omega,
        finiteSchedule_last_collision_reads, recoveryColor_eq_bits, certifiedColor_bits, Nat.mod_eq_of_lt hj]
      exact recoveryColor_aligned_check ⟨j, hj⟩
    · rw [show 12940 + scheduleTime f n + j = 13044 + scheduleTime f n + (j - 104) by omega,
        (finiteSchedule_standard f n).2, standardColor_eq_certifiedColor]
      have he : (j - 104) % 104 = j % 104 := by omega
      simp only [certifiedColor, he]

theorem growing_finite_exact_highway_start (n : Nat) :
    HighwayFrom (variableObstacles (schedulePrefix (fun i => i) n))
        (12915 + 52 * (n * (n + 7)) + 132 * n) 104 (-2, -2) ∧
      forall T v, HighwayFrom (variableObstacles (schedulePrefix (fun i => i) n)) T 104 v ->
        12915 + 52 * (n * (n + 7)) + 132 * n <= T := by
  simpa only [growing_time_formula, Nat.add_assoc] using finiteSchedule_exact_highway_start (fun i => i) n

end LangtonsAnt
