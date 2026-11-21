import ExactVariableRecovery

namespace LangtonsAnt

-- An empty gap list denotes one obstacle; the three listed gaps denote four obstacles.
example : variableCells [] = [(-4, -4)] := by decide +kernel
example : (variableCells [0, 3, 1]).map (addPoint chainOrigin) =
    [(-68, -42), (-76, -50), (-90, -64), (-100, -74)] := by decide +kernel
example : (variableCells [0, 3, 1]).length = 4 := by decide +kernel
example : (variableCells [0, 3, 1]).Nodup := variableCells_distinct _

example : (variableObstacles [0, 3, 1]).board (-90, -64) = true := by decide +kernel
example : (variableObstacles [0, 3, 1]).board (-84, -58) = false := by decide +kernel
example : (variableObstacles [0, 3, 1]).board (-110, -84) = false := by decide +kernel

example : StandardHighwayFrom (variableObstacles []) 13044 (-2, -2) := variableObstacles_standard []
example : StandardHighwayFrom (variableObstacles [0, 3, 1]) 15104 (-2, -2) :=
  variableObstacles_standard [0, 3, 1]

example (gaps : List Nat) : FiniteSupport (variableObstacles gaps).board ∧
    StandardHighwayFrom (variableObstacles gaps)
      (12496 + 548 * (gaps.length + 1) + 104 * gaps.sum) (-2, -2) :=
  ⟨variableObstacles_finite gaps, variableObstacles_standard gaps⟩

example : growingObstacles.board (-86, -60) = true := by
  apply (growingObstacles_black _).mpr
  exact ⟨2, rfl⟩

example : growingObstacles.board (-86, -59) = false := by
  cases h : growingObstacles.board (-86, -59)
  · rfl
  · obtain ⟨n, hn⟩ := (growingObstacles_black _).mp h
    simp only [Prod.mk.injEq] at hn
    omega

example : (run growingObstacles 13804).pos = (-86, -60) :=
  scheduledObstacles_visits (fun n => n) 2

example (T Q : Nat) (hQ : 0 < Q) (v : Point) : ¬HighwayFrom growingObstacles T Q v :=
  growingObstacles_no_highway T Q hQ v

example (T Q : Nat) (hQ : 0 < Q) :
    ¬(forall t, T <= t -> readColor growingObstacles (t + Q) = readColor growingObstacles t) :=
  growingObstacles_no_read_period T Q hQ

-- The criterion does not require monotonicity: every second gap can be zero.
example (T Q : Nat) (hQ : 0 < Q) (v : Point) :
    ¬HighwayFrom (scheduledObstacles (fun n => if n % 2 = 0 then n else 0)) T Q v := by
  apply scheduledObstacles_no_highway _ ?_ T Q hQ v
  intro N B
  refine ⟨2 * (N + B), by omega, ?_⟩
  have he : 2 * (N + B) % 2 = 0 := by omega
  simp only [he, ite_true]
  omega

example : StandardHighwayFrom (variableObstacles (schedulePrefix (fun i => i) 3)) 15000 (-2, -2) :=
  (growing_finite_truncations_standard 3).2

example (f : Nat -> Nat) (N n j : Nat) (hn : N <= n) (hj : j <= N) :
    (run (variableObstacles (schedulePrefix f n)) j).pos = (run (scheduledObstacles f) j).pos ∧
    (run (variableObstacles (schedulePrefix f n)) j).dir = (run (scheduledObstacles f) j).dir ∧
    readColor (variableObstacles (schedulePrefix f n)) j = readColor (scheduledObstacles f) j :=
  finiteSchedules_match_infinite_prefix f N n hn j hj

-- First contact and eventual onset are different events, with an exact 311-step gap.
example : (run (variableObstacles []) 12604).pos = (-68, -42) ∧
    forall j, j < 12604 -> (run (variableObstacles []) j).pos ≠ (-68, -42) :=
  finiteSchedule_first_visits (fun _ => 0) 0 0 (by decide)

example : HighwayFrom (variableObstacles []) 12915 104 (-2, -2) :=
  finiteSchedule_exact_highway (fun _ => 0) 0

example (v : Point) : ¬HighwayFrom (variableObstacles []) 12914 104 v := by
  intro h
  have hh := finiteSchedule_exact_start_lower_bound (fun _ => 0) 0 12914 v h
  change 12915 <= 12914 at hh
  omega

example : StandardHighwayFrom (variableObstacles []) 12940 (-2, -2) :=
  finiteSchedule_earlier_standard (fun _ => 0) 0

example : (run (variableObstacles (schedulePrefix (fun i => i) 3)) 14560).pos = (-98, -72) :=
  (finiteSchedule_first_visits (fun i => i) 3 3 (by decide)).1

example : HighwayFrom (variableObstacles (schedulePrefix (fun i => i) 3)) 14871 104 (-2, -2) :=
  finiteSchedule_exact_highway (fun i => i) 3

example : StandardHighwayFrom (variableObstacles (schedulePrefix (fun i => i) 3)) 14896 (-2, -2) :=
  finiteSchedule_earlier_standard (fun i => i) 3

example : HighwayFrom (variableObstacles [0, 3, 1]) 14975 104 (-2, -2) :=
  finiteSchedule_exact_highway (fun i => [0, 3, 1][i]?.getD 0) 3

example (i j : Nat) (hj : j < 12604 + scheduleTime (fun k => k) i) :
    (run growingObstacles j).pos ≠
      (-68 - 2 * (scheduleDistance (fun k => k) i : Int), -42 - 2 * (scheduleDistance (fun k => k) i : Int)) :=
  (scheduledObstacles_first_visits (fun k => k) i).2 j hj

end LangtonsAnt
