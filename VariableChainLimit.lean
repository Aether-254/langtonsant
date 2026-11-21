import VariableFiniteObstacles
import AperiodicObstacleChain
import InfiniteChainLimit

namespace LangtonsAnt

def schedulePrefix (f : Nat -> Nat) (n : Nat) : List Nat := (List.range n).map f

theorem schedulePrefix_succ (f : Nat -> Nat) (n : Nat) :
    schedulePrefix f (n + 1) = f 0 :: schedulePrefix (scheduleTail f 1) n := by
  simp only [schedulePrefix, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 2
  funext i
  simp [scheduleTail, Nat.add_comm]

theorem variableCells_schedulePrefix (f : Nat -> Nat) (n : Nat) :
    variableCells (schedulePrefix f n) = (List.range (n + 1)).map (schedulePoint f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [schedulePrefix_succ, variableCells, ih]
    rw [List.range_succ_eq_map (n := n + 1), List.map_cons, List.map_map, List.map_map]
    change chainHead :: (List.range (n + 1)).map (fun i => addPoint (spacedShift (f 0)) (schedulePoint (scheduleTail f 1) i)) =
      chainHead :: (List.range (n + 1)).map (fun i => schedulePoint f (i + 1))
    have he : (fun i => addPoint (spacedShift (f 0)) (schedulePoint (scheduleTail f 1) i)) =
        fun i => schedulePoint f (i + 1) := funext (fun i => (schedulePoint_succ f i).symm)
    rw [he]

theorem finiteSchedule_black (f : Nat -> Nat) (n : Nat) (p : Point) :
    (variableObstacles (schedulePrefix f n)).board p = true ↔ exists i : Nat, i <= n ∧
      p = (-68 - 2 * (scheduleDistance f i : Int), -42 - 2 * (scheduleDistance f i : Int)) := by
  rw [variableObstacles_black, variableCells_schedulePrefix, List.map_map]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, hp⟩
    refine ⟨i, by omega, ?_⟩
    rw [← hp]
    apply Prod.ext <;> simp [chainOrigin, schedulePoint, scheduleOffset, addPoint, chainHead] <;> omega
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, by omega, ?_⟩
    apply Prod.ext <;> simp [chainOrigin, schedulePoint, scheduleOffset, addPoint, chainHead] <;> omega

theorem variableRecovery_schedulePrefix (f : Nat -> Nat) (n : Nat) :
    variableRecovery (schedulePrefix f n) = scheduleTime f n + 548 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [schedulePrefix_succ, variableRecovery, ih, scheduleTime_tail]
    omega

theorem finiteSchedule_standard (f : Nat -> Nat) (n : Nat) :
    StandardHighwayFrom (variableObstacles (schedulePrefix f n)) (13044 + scheduleTime f n) (-2, -2) := by
  have h := variableObstacles_standard (schedulePrefix f n)
  have hr := variableRecovery_schedulePrefix f n
  have hf := variableRecovery_formula (schedulePrefix f n)
  have ht : 12496 + 548 * ((schedulePrefix f n).length + 1) + 104 * (schedulePrefix f n).sum =
      13044 + scheduleTime f n := by omega
  rw [ht] at h
  exact h

theorem finiteSchedule_board_agreement (f : Nat -> Nat) (N n : Nat) (hn : N <= n) (p : Point)
    (hp : -(N : Int) <= p.1) :
    (variableObstacles (schedulePrefix f n)).board p = (scheduledObstacles f).board p := by
  have he : (variableObstacles (schedulePrefix f n)).board p = true ↔ (scheduledObstacles f).board p = true := by
    rw [finiteSchedule_black, scheduledObstacles_black]
    constructor
    · rintro ⟨i, _, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_, hi⟩
      have hd := scheduleDistance_ge f i
      rw [hi] at hp
      change -(N : Int) <= -68 - 2 * (scheduleDistance f i : Int) at hp
      omega
  cases hf : (variableObstacles (schedulePrefix f n)).board p <;>
    cases hi : (scheduledObstacles f).board p <;> simp_all

/-- Every finite observation window agrees once sufficiently many initial obstacles are retained. -/
theorem finiteSchedules_match_infinite_prefix (f : Nat -> Nat) (N n : Nat) (hn : N <= n) :
    forall j, j <= N ->
      (run (variableObstacles (schedulePrefix f n)) j).pos = (run (scheduledObstacles f) j).pos ∧
      (run (variableObstacles (schedulePrefix f n)) j).dir = (run (scheduledObstacles f) j).dir ∧
      readColor (variableObstacles (schedulePrefix f n)) j = readColor (scheduledObstacles f) j := by
  have hb (j : Nat) (hj : j <= N) :
      (variableObstacles (schedulePrefix f n)).board (run (scheduledObstacles f) j).pos =
        (scheduledObstacles f).board (run (scheduledObstacles f) j).pos := by
    apply finiteSchedule_board_agreement f N n hn
    have hw := run_x_lower_bound (scheduledObstacles f) j
    change (0 : Int) - (j : Int) <= (run (scheduledObstacles f) j).pos.1 at hw
    omega
  intro j hj
  have hc := finite_run_coupling (s := variableObstacles (schedulePrefix f n)) (t := scheduledObstacles f)
    rfl rfl j (fun i hi => hb i (by omega))
  refine ⟨hc.1, hc.2.1, ?_⟩
  unfold readColor
  rw [hc.1]
  exact hc.2.2 _ (hb j hj)

theorem growing_finite_truncations_standard (n : Nat) :
    FiniteSupport (variableObstacles (schedulePrefix (fun i => i) n)).board ∧
      StandardHighwayFrom (variableObstacles (schedulePrefix (fun i => i) n))
        (13044 + 52 * (n * (n + 7)) + 132 * n) (-2, -2) := by
  refine ⟨variableObstacles_finite _, ?_⟩
  have h := finiteSchedule_standard (fun i => i) n
  simpa only [growing_time_formula, Nat.add_assoc] using h

end LangtonsAnt
