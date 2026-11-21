import VariableInfiniteObstacles

namespace LangtonsAnt

theorem scheduledObstacles_collision_reads (f : Nat -> Nat) (n j : Nat) (hj : j < 548) :
    readColor (scheduledObstacles f) (12496 + scheduleTime f n + j) = obstacleColor j := by
  have he := (scheduledObstacles_entries f n).unshift
  rw [scheduleMask_split (scheduleTail f n), scheduleTail_succ] at he
  have hh := variableBlock_collision_reads (scheduleMask_ahead (scheduleTail f (n + 1))) (f n) he j hj
  rw [translate_readColor] at hh
  simpa only [readColor, ← run_add] using hh

theorem scheduledObstacles_standard_reads (f : Nat -> Nat) (n j : Nat) (hj : j < 104 * f n) :
    readColor (scheduledObstacles f) (12496 + scheduleTime f n + 548 + j) = certifiedColor j := by
  have he := (scheduledObstacles_entries f n).unshift
  rw [scheduleMask_split (scheduleTail f n), scheduleTail_succ] at he
  have hh := variableBlock_standard_reads (scheduleMask_ahead (scheduleTail f (n + 1))) (f n) he j hj
  rw [translate_readColor] at hh
  simpa only [readColor, ← run_add, Nat.add_assoc] using hh

theorem scheduledObstacles_marker (f : Nat -> Nat) (n : Nat) :
    HasCollisionMarker (readColor (scheduledObstacles f)) (12496 + scheduleTime f n + 107) := by
  intro j
  have hh := collisionMarker_at_start 0 j
  rw [spacedColor_common_collision 0 _ (by omega)] at hh
  rw [Nat.add_assoc, scheduledObstacles_collision_reads f n _ (by omega)]
  exact hh

set_option maxRecDepth 100000 in
theorem scheduledObstacles_visits (f : Nat -> Nat) (n : Nat) :
    (run (scheduledObstacles f) (12604 + scheduleTime f n)).pos =
      (-68 - 2 * (scheduleDistance f n : Int), -42 - 2 * (scheduleDistance f n : Int)) := by
  let v := addPoint chainOrigin (scheduleOffset f n)
  have he := (scheduledObstacles_entries f n).unshift
  rw [scheduleMask_split (scheduleTail f n), scheduleTail_succ] at he
  have hr := (variableBlock_collision_prefix (scheduleMask_ahead (scheduleTail f (n + 1)))
    (f n) he 108 (by decide)).translate v
  rw [translate_run, translate_add, addPoint_subPoint, translate_zero, ← run_add] at hr
  have hp := hr.pos
  change (run (scheduledObstacles f) (12496 + scheduleTime f n + 108)).pos =
    addPoint v (run chainCollisionSeed.toState 108).pos at hp
  have hc : (run chainCollisionSeed.toState 108).pos = chainHead := by
    have hh : (chainCollisionSeed.run 108).pos = (run chainCollisionSeed.toState 108).pos :=
      congrArg State.pos (chainCollisionSeed.toState_run 108)
    exact hh.symm.trans chainCollision_contact_check
  rw [hc, show 12496 + scheduleTime f n + 108 = 12604 + scheduleTime f n by omega] at hp
  rw [hp]
  apply Prod.ext <;> simp [v, chainOrigin, scheduleOffset, addPoint, chainHead] <;> omega

theorem certifiedColor_no_marker (n : Nat) : ¬HasCollisionMarker certifiedColor n := by
  intro h
  apply collisionMarker_checks.2.2 ⟨n % 104, Nat.mod_lt _ (by decide)⟩
  intro j
  have hh := h j
  simpa only [certifiedColor, Nat.add_mod, Nat.mod_mod] using hh

theorem HasCollisionMarker.shift_period {f : Nat -> Bool} {T Q n : Nat}
    (h : forall t, T <= t -> f (t + Q) = f t) (hn : T <= n)
    (hm : HasCollisionMarker f n) (m : Nat) : HasCollisionMarker f (n + Q * m) := by
  induction m with
  | zero => simpa only [Nat.mul_zero, Nat.add_zero] using hm
  | succ m ih =>
    intro j
    rw [Nat.mul_succ, show n + (Q * m + Q) + j.val = (n + Q * m + j.val) + Q by omega,
      h _ (by omega)]
    exact ih j

/-- Arbitrarily late, arbitrarily long gaps force the read sequence to be nonperiodic on every tail. -/
theorem scheduledObstacles_no_read_period (f : Nat -> Nat)
    (hunbounded : forall N B : Nat, exists n, N <= n ∧ B <= f n)
    (T Q : Nat) (hQ : 0 < Q) :
    ¬(forall t, T <= t -> readColor (scheduledObstacles f) (t + Q) = readColor (scheduledObstacles f) t) := by
  intro h
  obtain ⟨n, hn, hlarge⟩ := hunbounded T (Q + 1)
  have ht := scheduleTime_ge f n
  have hm := (scheduledObstacles_marker f n).shift_period h (by omega) (441 / Q + 1)
  let a := Q * (441 / Q + 1)
  have ha : 441 < a ∧ a <= 441 + Q := by
    have hd := Nat.div_add_mod 441 Q
    have hr := Nat.mod_lt 441 hQ
    dsimp [a]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  let j0 := a - 441
  have hj0 : j0 <= Q := by dsimp [j0]; omega
  apply certifiedColor_no_marker j0
  intro j
  have hs := scheduledObstacles_standard_reads f n (j0 + j.val) (by omega)
  have hj := hm j
  change readColor (scheduledObstacles f) (12496 + scheduleTime f n + 107 + a + j.val) = _ at hj
  have he : 12496 + scheduleTime f n + 107 + a + j.val =
      12496 + scheduleTime f n + 548 + (j0 + j.val) := by dsimp [j0]; omega
  rw [he, hs] at hj
  exact hj

theorem scheduledObstacles_no_highway (f : Nat -> Nat)
    (hunbounded : forall N B : Nat, exists n, N <= n ∧ B <= f n)
    (T Q : Nat) (hQ : 0 < Q) (v : Point) : ¬HighwayFrom (scheduledObstacles f) T Q v := by
  intro h
  exact scheduledObstacles_no_read_period f hunbounded T Q hQ (fun _ ht => h.reads_periodic ht)

noncomputable def growingObstacles : State := scheduledObstacles (fun n => n)

theorem growingObstacles_no_read_period (T Q : Nat) (hQ : 0 < Q) :
    ¬(forall t, T <= t -> readColor growingObstacles (t + Q) = readColor growingObstacles t) := by
  apply scheduledObstacles_no_read_period (fun n => n) ?_ T Q hQ
  intro N B
  exact ⟨N + B, by omega, by omega⟩

theorem growingObstacles_no_highway (T Q : Nat) (hQ : 0 < Q) (v : Point) :
    ¬HighwayFrom growingObstacles T Q v := by
  apply scheduledObstacles_no_highway (fun n => n) ?_ T Q hQ v
  intro N B
  exact ⟨N + B, by omega, by omega⟩

theorem growingObstacles_not_eventuallyStandard : ¬EventuallyStandard growingObstacles := by
  rintro ⟨T, v, _, h⟩
  exact growingObstacles_no_highway T 104 (by decide) v h.1

theorem growingObstacles_not_finite : ¬FiniteSupport growingObstacles.board :=
  scheduledObstacles_not_finite (fun n => n)

theorem growing_distance_formula (n : Nat) :
    2 * scheduleDistance (fun i => i) n = n * (n + 7) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scheduleDistance, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ih ⊢
    omega

theorem growingObstacles_black (p : Point) : growingObstacles.board p = true ↔ exists n : Nat,
    p = (-68 - (n : Int) * ((n : Int) + 7), -42 - (n : Int) * ((n : Int) + 7)) := by
  have he (n : Nat) :
      (-68 - 2 * (scheduleDistance (fun i => i) n : Int), -42 - 2 * (scheduleDistance (fun i => i) n : Int)) =
      (-68 - (n : Int) * ((n : Int) + 7), -42 - (n : Int) * ((n : Int) + 7)) := by
    have hh := congrArg (fun x : Nat => (x : Int)) (growing_distance_formula n)
    simp only [Int.natCast_mul, Int.natCast_add] at hh
    change 2 * (scheduleDistance (fun i => i) n : Int) = (n : Int) * ((n : Int) + 7) at hh
    apply Prod.ext <;> simp only [hh]
  simpa only [growingObstacles, he] using scheduledObstacles_black (fun n => n) p

theorem schedule_time_distance (f : Nat -> Nat) (n : Nat) :
    scheduleTime f n = 104 * scheduleDistance f n + 132 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scheduleTime, scheduleDistance, spacedPeriod, ih, Nat.mul_add]
    omega

theorem growing_time_formula (n : Nat) :
    scheduleTime (fun i => i) n = 52 * (n * (n + 7)) + 132 * n := by
  rw [schedule_time_distance, ← growing_distance_formula]
  omega

end LangtonsAnt
