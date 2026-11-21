import VariableFirstVisits

namespace LangtonsAnt

theorem finiteSchedule_marker (f : Nat -> Nat) (n i : Nat) (hi : i <= n) :
    HasCollisionMarker (readColor (variableObstacles (schedulePrefix f n)))
      (12496 + scheduleTime f i + 107) := by
  intro j
  have hh := collisionMarker_at_start 0 j
  rw [spacedColor_common_collision 0 _ (by omega)] at hh
  rw [Nat.add_assoc, finiteSchedule_collision_reads f n i hi _ (by omega)]
  exact hh

theorem StandardHighwayFrom.no_collisionMarker {s : State} {U : Nat} {v : Point}
    (h : StandardHighwayFrom s U v) (m : Nat) (hm : U <= m) :
    ¬HasCollisionMarker (readColor s) m := by
  intro hc
  apply certifiedColor_no_marker (m - U)
  intro j
  have hh := hc j
  rw [show m + j.val = U + (m - U + j.val) by omega, h.2,
    standardColor_eq_certifiedColor] at hh
  exact hh

/-- A marker absent from the eventual standard word cannot lie in any periodic tail. -/
theorem StandardHighwayFrom.periodic_tail_after_marker {s : State} {U : Nat} {v : Point}
    (h : StandardHighwayFrom s U v) {m : Nat} (hm : HasCollisionMarker (readColor s) m)
    {T Q : Nat} (hQ : 0 < Q)
    (hp : forall t, T <= t -> readColor s (t + Q) = readColor s t) : m < T := by
  by_cases ht : T <= m
  · have hs := hm.shift_period hp ht U
    have hu : U <= m + Q * U := by
      have hmul := Nat.mul_le_mul_right U hQ
      omega
    exact False.elim (h.no_collisionMarker _ hu hs)
  · omega

/-- No positive-period highway can have begun strictly before the last first contact. -/
theorem finiteSchedule_highway_start_lower_bound (f : Nat -> Nat) (n T Q : Nat) (hQ : 0 < Q)
    (v : Point) (h : HighwayFrom (variableObstacles (schedulePrefix f n)) T Q v) :
    12604 + scheduleTime f n <= T := by
  have hh := (finiteSchedule_standard f n).periodic_tail_after_marker
    (finiteSchedule_marker f n n (Nat.le_refl _)) hQ (fun _ ht => h.reads_periodic ht)
  omega

theorem finiteSchedule_recovery_bounds (f : Nat -> Nat) (n : Nat) :
    StandardHighwayFrom (variableObstacles (schedulePrefix f n)) (13044 + scheduleTime f n) (-2, -2) ∧
    forall T Q, 0 < Q -> forall v,
      HighwayFrom (variableObstacles (schedulePrefix f n)) T Q v -> 12604 + scheduleTime f n <= T :=
  ⟨finiteSchedule_standard f n, finiteSchedule_highway_start_lower_bound f n⟩

/-- The earliest permanent 104-step highway starts in a window of width 440. -/
theorem finiteSchedule_earliest_highway (f : Nat -> Nat) (n : Nat) :
    exists T v, 12604 + scheduleTime f n <= T ∧ T <= 13044 + scheduleTime f n ∧
      HighwayFrom (variableObstacles (schedulePrefix f n)) T 104 v ∧
      forall t, t < T -> forall w, ¬HighwayFrom (variableObstacles (schedulePrefix f n)) t 104 w := by
  obtain ⟨T, ⟨v, hv⟩, hleast⟩ := exists_first_nat
    (fun T => exists v, HighwayFrom (variableObstacles (schedulePrefix f n)) T 104 v)
    ⟨13044 + scheduleTime f n, (-2, -2), (finiteSchedule_standard f n).1⟩
  have hT : T <= 13044 + scheduleTime f n := by
    by_cases ht : T <= 13044 + scheduleTime f n
    · exact ht
    · exact False.elim (hleast _ (by omega) ⟨(-2, -2), (finiteSchedule_standard f n).1⟩)
  exact ⟨T, v, finiteSchedule_highway_start_lower_bound f n T 104 (by decide) v hv,
    hT, hv, fun t ht w hw => hleast t ht ⟨w, hw⟩⟩

theorem growing_finite_earliest_highway (n : Nat) :
    exists T v, 12604 + 52 * (n * (n + 7)) + 132 * n <= T ∧
      T <= 13044 + 52 * (n * (n + 7)) + 132 * n ∧
      HighwayFrom (variableObstacles (schedulePrefix (fun i => i) n)) T 104 v ∧
      forall t, t < T -> forall w,
        ¬HighwayFrom (variableObstacles (schedulePrefix (fun i => i) n)) t 104 w := by
  simpa only [growing_time_formula, Nat.add_assoc] using finiteSchedule_earliest_highway (fun i => i) n

/-- A single fixed infinite schedule has finite truncations whose onset times diverge. -/
theorem finiteSchedule_onsets_unbounded (f : Nat -> Nat) (B : Nat) :
    exists n, FiniteSupport (variableObstacles (schedulePrefix f n)).board ∧
      StandardHighwayFrom (variableObstacles (schedulePrefix f n)) (13044 + scheduleTime f n) (-2, -2) ∧
      forall T Q, T <= B -> 0 < Q -> forall v,
        ¬HighwayFrom (variableObstacles (schedulePrefix f n)) T Q v := by
  refine ⟨B, variableObstacles_finite _, finiteSchedule_standard f B, ?_⟩
  intro T Q hT hQ v hv
  have hl := finiteSchedule_highway_start_lower_bound f B T Q hQ v hv
  have hg := scheduleTime_ge f B
  omega

end LangtonsAnt
