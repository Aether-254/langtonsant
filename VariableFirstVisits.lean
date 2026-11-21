import VariableChainLimit

namespace LangtonsAnt

set_option maxRecDepth 100000 in
theorem variableBlock_head_first {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState)) :
    (run s 108).pos = chainHead ∧ forall j, j < 108 -> (run s j).pos ≠ chainHead := by
  constructor
  · have hp := (variableBlock_collision_prefix ha k h 108 (by decide)).pos
    have he : (chainCollisionSeed.run 108).pos = (run chainCollisionSeed.toState 108).pos :=
      congrArg State.pos (chainCollisionSeed.toState_run 108)
    exact hp.trans (he.symm.trans chainCollision_contact_check)
  · intro j hj he
    have hp := (variableBlock_collision_prefix ha k h j (by omega)).pos
    have hr : (chainCollisionSeed.run j).pos = (run chainCollisionSeed.toState j).pos :=
      congrArg State.pos (chainCollisionSeed.toState_run j)
    exact chainCollision_first_check ⟨j, hj⟩ (hr.trans (hp.symm.trans he))

set_option maxRecDepth 100000 in
theorem variableBlock_tail_untouched {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState))
    (j : Nat) (hj : j < spacedPeriod k) :
    shiftedObstacles k mask (run s j).pos = false := by
  by_cases hc : j < 548
  · have hp := (variableBlock_collision_prefix ha k h j (by omega)).pos
    change (run s j).pos = (run chainCollisionSeed.toState j).pos at hp
    rw [hp]
    exact shiftedObstacles_avoid_collision ha k j hc
  · have hn : j - 548 < 104 * k := by simp only [spacedPeriod] at hj; omega
    have hp := (variableBlock_standard_prefix ha k h (j - 548) (by omega)).pos
    have ht : 548 + (j - 548) = j := by omega
    rw [ht] at hp
    change (run s j).pos = (run (translate chainShift highwaySeed.toState) (j - 548)).pos at hp
    rw [hp]
    exact shiftedObstacles_avoid_standard ha k (j - 548) hn

theorem schedulePoint_mem_prefix (f : Nat -> Nat) (n i : Nat) (hi : i <= n) :
    variableMask (schedulePrefix f n) (schedulePoint f i) = true := by
  simp only [variableMask, decide_eq_true_eq, variableCells_schedulePrefix, List.mem_map, List.mem_range]
  exact ⟨i, by omega, rfl⟩

/-- Each retained obstacle is reached at the specified time, and never earlier. -/
theorem finiteSchedule_normalized_first_visits (f : Nat -> Nat) (n : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (variableMask (schedulePrefix f n)) highwaySeed.toState)) :
    forall i, i <= n ->
      (run s (scheduleTime f i + 108)).pos = schedulePoint f i ∧
      forall j, j < scheduleTime f i + 108 -> (run s j).pos ≠ schedulePoint f i := by
  induction n generalizing f s with
  | zero =>
    intro i hi
    have he : i = 0 := by omega
    subst i
    change AgreesBelow 0 s (perturb (variableMask []) highwaySeed.toState) at h
    rw [variableMask_nil] at h
    exact variableBlock_head_first (by intro p hp; contradiction) 0 h
  | succ n ih =>
    rw [schedulePrefix_succ, variableMask_cons] at h
    intro i hi
    cases i with
    | zero => exact variableBlock_head_first (variableMask_ahead _) (f 0) h
    | succ i =>
      have hh := ih (scheduleTail f 1) (variableBlock_step (variableMask_ahead _) (f 0) h) i (by omega)
      constructor
      · have hp := hh.1
        rw [translate_run, ← run_add] at hp
        rw [scheduleTime_tail, schedulePoint_succ, Nat.add_assoc]
        change addPoint (subPoint (0, 0) (spacedShift (f 0)))
          (run s (spacedPeriod (f 0) + (scheduleTime (scheduleTail f 1) i + 108))).pos =
          schedulePoint (scheduleTail f 1) i at hp
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        apply Prod.ext <;> simp only [addPoint, subPoint] at hx hy ⊢ <;> omega
      · intro j hj he
        rw [scheduleTime_tail] at hj
        rw [schedulePoint_succ] at he
        by_cases hearly : j < spacedPeriod (f 0)
        · have hu := variableBlock_tail_untouched (variableMask_ahead _) (f 0) h j hearly
          rw [he] at hu
          simp only [shiftedObstacles, subPoint_addPoint] at hu
          have hm := schedulePoint_mem_prefix (scheduleTail f 1) n i (by omega)
          rw [hm] at hu
          contradiction
        · apply hh.2 (j - spacedPeriod (f 0)) (by omega)
          rw [translate_run, ← run_add,
            show spacedPeriod (f 0) + (j - spacedPeriod (f 0)) = j by omega]
          change addPoint (subPoint (0, 0) (spacedShift (f 0))) (run s j).pos = _
          rw [he]
          apply Prod.ext <;> simp [addPoint, subPoint] <;> omega

theorem finiteSchedule_normalized_collision_reads (f : Nat -> Nat) (n : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (variableMask (schedulePrefix f n)) highwaySeed.toState)) :
    forall i, i <= n -> forall j, j < 548 -> readColor s (scheduleTime f i + j) = obstacleColor j := by
  induction n generalizing f s with
  | zero =>
    intro i hi j hj
    have he : i = 0 := by omega
    subst i
    change AgreesBelow 0 s (perturb (variableMask []) highwaySeed.toState) at h
    rw [variableMask_nil] at h
    simpa only [scheduleTime, Nat.zero_add] using
      variableBlock_collision_reads (by intro p hp; contradiction) 0 h j hj
  | succ n ih =>
    rw [schedulePrefix_succ, variableMask_cons] at h
    intro i hi j hj
    cases i with
    | zero =>
      simpa only [scheduleTime, Nat.zero_add] using
        variableBlock_collision_reads (variableMask_ahead _) (f 0) h j hj
    | succ i =>
      have hh := ih (scheduleTail f 1) (variableBlock_step (variableMask_ahead _) (f 0) h) i (by omega) j hj
      rw [translate_readColor] at hh
      simpa only [readColor, ← run_add, scheduleTime_tail, Nat.add_assoc] using hh

theorem finiteSchedule_collision_reads (f : Nat -> Nat) (n i : Nat) (hi : i <= n)
    (j : Nat) (hj : j < 548) :
    readColor (variableObstacles (schedulePrefix f n)) (12496 + scheduleTime f i + j) = obstacleColor j := by
  have he : AgreesBelow (weight chainOrigin) (run (variableObstacles (schedulePrefix f n)) 12496)
      (translate chainOrigin (perturb (variableMask (schedulePrefix f n)) highwaySeed.toState)) :=
    aheadMask_blank_entry (variableMask_ahead _)
  have hh := finiteSchedule_normalized_collision_reads f n he.unshift i hi j hj
  rw [translate_readColor] at hh
  simpa only [readColor, ← run_add, Nat.add_assoc] using hh

theorem finiteSchedule_first_visits (f : Nat -> Nat) (n i : Nat) (hi : i <= n) :
    (run (variableObstacles (schedulePrefix f n)) (12604 + scheduleTime f i)).pos =
      (-68 - 2 * (scheduleDistance f i : Int), -42 - 2 * (scheduleDistance f i : Int)) ∧
    forall j, j < 12604 + scheduleTime f i ->
      (run (variableObstacles (schedulePrefix f n)) j).pos ≠
        (-68 - 2 * (scheduleDistance f i : Int), -42 - 2 * (scheduleDistance f i : Int)) := by
  have he : AgreesBelow (weight chainOrigin) (run (variableObstacles (schedulePrefix f n)) 12496)
      (translate chainOrigin (perturb (variableMask (schedulePrefix f n)) highwaySeed.toState)) :=
    aheadMask_blank_entry (variableMask_ahead _)
  have hh := finiteSchedule_normalized_first_visits f n he.unshift i hi
  have hp : addPoint chainOrigin (schedulePoint f i) =
      (-68 - 2 * (scheduleDistance f i : Int), -42 - 2 * (scheduleDistance f i : Int)) := by
    apply Prod.ext <;> simp [chainOrigin, schedulePoint, scheduleOffset, addPoint, chainHead] <;> omega
  constructor
  · have hv := hh.1
    rw [translate_run, ← run_add,
      show 12496 + (scheduleTime f i + 108) = 12604 + scheduleTime f i by omega] at hv
    rw [← hp]
    change addPoint (subPoint (0, 0) chainOrigin)
      (run (variableObstacles (schedulePrefix f n)) (12604 + scheduleTime f i)).pos = schedulePoint f i at hv
    have hx := congrArg Prod.fst hv
    have hy := congrArg Prod.snd hv
    apply Prod.ext <;> simp only [addPoint, subPoint] at hx hy ⊢ <;> omega
  · intro j hj hv
    rw [← hp] at hv
    by_cases hearly : j < 12496
    · have hr := run_perturb_avoids (fun p => variableMask (schedulePrefix f n) (subPoint p chainOrigin))
        blank j (fun k hk => aheadMask_avoids_blank_prefix (variableMask_ahead _) k (by omega))
      have hrp := congrArg State.pos hr
      have hpos : (run (variableObstacles (schedulePrefix f n)) j).pos = (run blank j).pos := hrp
      have hu := aheadMask_avoids_blank_prefix (variableMask_ahead (schedulePrefix f n)) j hearly
      rw [← hpos, hv, subPoint_addPoint, schedulePoint_mem_prefix f n i hi] at hu
      contradiction
    · apply hh.2 (j - 12496) (by omega)
      rw [translate_run, ← run_add, show 12496 + (j - 12496) = j by omega]
      change addPoint (subPoint (0, 0) chainOrigin) (run (variableObstacles (schedulePrefix f n)) j).pos = _
      rw [hv]
      apply Prod.ext <;> simp [addPoint, subPoint] <;> omega

/-- First visits also hold for the infinite schedule, by finite-window coupling. -/
theorem scheduledObstacles_first_visits (f : Nat -> Nat) (i : Nat) :
    (run (scheduledObstacles f) (12604 + scheduleTime f i)).pos =
      (-68 - 2 * (scheduleDistance f i : Int), -42 - 2 * (scheduleDistance f i : Int)) ∧
    forall j, j < 12604 + scheduleTime f i -> (run (scheduledObstacles f) j).pos ≠
      (-68 - 2 * (scheduleDistance f i : Int), -42 - 2 * (scheduleDistance f i : Int)) := by
  refine ⟨scheduledObstacles_visits f i, ?_⟩
  intro j hj he
  have hp := (finiteSchedules_match_infinite_prefix f j (i + j) (by omega) j (by omega)).1
  exact (finiteSchedule_first_visits f (i + j) i (by omega)).2 j hj (hp.trans he)

end LangtonsAnt
