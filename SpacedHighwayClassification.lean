import SpacedHighwayPeriod

namespace LangtonsAnt

theorem spacedSeed_collision_reads (k n : Nat) (hn : n < 548) :
    readColor (spacedSeed k) n = obstacleColor n := by
  have ht : spacedTail k (run chainCollisionSeed.toState n).pos = false := by
    cases hc : spacedTail k (run chainCollisionSeed.toState n).pos
    · rfl
    · have hw := (spacedTail_geometry hc).2.2
      have hb := (chainCollision_range n hn).1
      omega
  have he : readColor (spacedSeed k) n = readColor chainCollisionSeed.toState n := by
    unfold readColor
    rw [spaced_collision_prefix k n (by omega)]
    change ((run chainCollisionSeed.toState n).board (run chainCollisionSeed.toState n).pos ^^
      spacedTail k (run chainCollisionSeed.toState n).pos) = _
    rw [ht, Bool.xor_false]
  rw [he]
  symm
  simpa only [obstacleColor, obstacleWord, Nat.mod_eq_of_lt hn, List.getElem?_toArray] using
    finiteReadWord_get chainCollisionSeed 548 n hn

set_option maxRecDepth 100000 in
theorem spacedSeed_standard_reads (k n : Nat) (hn : n < 104 * k) :
    readColor (spacedSeed k) (548 + n) = certifiedColor n := by
  have hm := spaced_standard_prefix k n (by omega)
  have hb := (highwaySeed_certificate.translate chainShift).all_bounded n
  have he : readColor (spacedSeed k) (548 + n) =
      readColor (translate chainShift highwaySeed.toState) n := by
    unfold readColor
    rw [hm.pos]
    have hc := hm.board (run (translate chainShift highwaySeed.toState) n).pos hb
    simpa only [perturb, spacedTail_avoids_standard k n hn, Bool.xor_false] using hc
  rw [he, translate_readColor, highwaySeed_exact_reads]

theorem spacedSeed_exact_reads (k n : Nat) : readColor (spacedSeed k) n = spacedColor k n := by
  rw [(spaced_certificate k).reads n]
  unfold spacedColor
  by_cases hn : n % spacedPeriod k < 548
  · rw [ite_eq_left hn, spacedSeed_collision_reads k _ hn]
  · rw [ite_eq_right hn]
    have hmod : n % spacedPeriod k < spacedPeriod k := Nat.mod_lt _ (by unfold spacedPeriod; omega)
    have hupper : n % spacedPeriod k < 548 + 104 * k := hmod
    have hlen : n % spacedPeriod k - 548 < 104 * k := by omega
    have he : n % spacedPeriod k = 548 + (n % spacedPeriod k - 548) := by omega
    calc
      readColor (spacedSeed k) (n % spacedPeriod k) =
          readColor (spacedSeed k) (548 + (n % spacedPeriod k - 548)) := congrArg _ he
      _ = _ := spacedSeed_standard_reads k _ hlen

theorem spacedObstacles_exact_reads (k n : Nat) :
    readColor (spacedObstacles k) (12496 + n) = spacedColor k n := by
  rw [spacedObstacles_reads, spacedSeed_exact_reads]
  simp only [spacedColor, Nat.mod_mod]

/-- The six-read marker occurs exactly once in each period, on the actual infinite trajectory. -/
theorem spacedObstacles_marker_iff (k n : Nat) :
    HasCollisionMarker (fun j => readColor (spacedObstacles k) (12496 + j)) n ↔
      n % spacedPeriod k = 107 := by
  have he : (fun j => readColor (spacedObstacles k) (12496 + j)) = spacedColor k :=
    funext (spacedObstacles_exact_reads k)
  rw [he, collisionMarker_iff]

theorem spacedColor_eventual_period_dvd (k U Q : Nat)
    (h : forall n, U <= n -> spacedColor k (n + Q) = spacedColor k n) :
    spacedPeriod k ∣ Q := by
  have hP : 107 < spacedPeriod k := by unfold spacedPeriod; omega
  let n := spacedPeriod k * U + 107
  have hn : U <= n := by
    have hh := Nat.le_mul_of_pos_left U (show 0 < spacedPeriod k by omega)
    dsimp [n]
    omega
  have hm : HasCollisionMarker (spacedColor k) n := by
    apply (collisionMarker_iff k n).mpr
    simp only [n, Nat.mul_add_mod, Nat.mod_eq_of_lt hP]
  have hshift : HasCollisionMarker (spacedColor k) (n + Q) := by
    intro j
    rw [show n + Q + j.val = (n + j.val) + Q by omega, h _ (by omega)]
    exact hm j
  have he := (collisionMarker_iff k (n + Q)).mp hshift
  have he' : (107 + Q) % spacedPeriod k = 107 := by
    simpa only [n, Nat.add_assoc, Nat.mul_add_mod] using he
  have hd : spacedPeriod k ∣ (107 + Q) - (107 + Q) % spacedPeriod k := Nat.dvd_sub_mod _
  simpa only [he', Nat.add_sub_cancel_left] using hd

theorem spacedObstacles_read_period_dvd (k T Q : Nat)
    (h : forall n, T <= n -> readColor (spacedObstacles k) (n + Q) =
      readColor (spacedObstacles k) n) : spacedPeriod k ∣ Q := by
  apply spacedColor_eventual_period_dvd k T Q
  intro n hn
  have hh := h (12496 + n) (by omega)
  rw [Nat.add_assoc, spacedObstacles_exact_reads, spacedObstacles_exact_reads] at hh
  exact hh

theorem spacedObstacles_highway_period_dvd (k : Nat) {T Q : Nat} {v : Point}
    (h : HighwayFrom (spacedObstacles k) T Q v) : spacedPeriod k ∣ Q :=
  spacedObstacles_read_period_dvd k T Q (fun _ hn => h.reads_periodic hn)

set_option maxRecDepth 100000 in
theorem spacedObstacles_read_period_iff (k Q : Nat) :
    (exists T, forall n, T <= n -> readColor (spacedObstacles k) (n + Q) =
      readColor (spacedObstacles k) n) ↔ spacedPeriod k ∣ Q := by
  constructor
  · rintro ⟨T, h⟩
    exact spacedObstacles_read_period_dvd k T Q h
  · intro h
    refine ⟨12496, ?_⟩
    intro n hn
    have hmod : Q % spacedPeriod k = 0 := Nat.mod_eq_zero_of_dvd h
    have ht : n = 12496 + (n - 12496) := by omega
    rw [ht, Nat.add_assoc, spacedObstacles_exact_reads, spacedObstacles_exact_reads]
    simp only [spacedColor, Nat.add_mod, hmod, Nat.add_zero, Nat.mod_mod]

theorem spacedObstacles_minimal_read_period (k T Q : Nat) (hQ : 0 < Q) (hsmall : Q < spacedPeriod k) :
    ¬(forall n, T <= n -> readColor (spacedObstacles k) (n + Q) = readColor (spacedObstacles k) n) := by
  intro h
  have hh := Nat.le_of_dvd hQ (spacedObstacles_read_period_dvd k T Q h)
  omega

theorem spacedObstacles_no_short_tail (k T Q : Nat) (hQ : 0 < Q) (hsmall : Q < spacedPeriod k) (v : Point) :
    ¬HighwayFrom (spacedObstacles k) T Q v := by
  intro h
  have hh := Nat.le_of_dvd hQ (spacedObstacles_highway_period_dvd k h)
  omega

theorem spacedObstacles_exact_minimal_period (k : Nat) :
    HighwayFrom (spacedObstacles k) 12496 (spacedPeriod k) (spacedShift k) ∧
      forall T Q v, 0 < Q -> Q < spacedPeriod k -> ¬HighwayFrom (spacedObstacles k) T Q v :=
  ⟨spacedObstacles_highway k, fun T Q v hQ hs => spacedObstacles_no_short_tail k T Q hQ hs v⟩

theorem HighwayFrom.multiple {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (m : Nat) : HighwayFrom s T (P * m) (offset v m) := by
  intro n hn
  induction m with
  | zero => simp [offset]
  | succ m ih =>
    have hh := h (n + P * m) (by omega)
    rw [Nat.mul_succ, ← Nat.add_assoc, hh.1, hh.2, ih.1, ih.2]
    constructor
    · apply Prod.ext <;> simp [offset, addPoint, Int.add_assoc]
    · rfl

/-- All eventual translation periods and displacements are multiples of the certified pair. -/
theorem spacedObstacles_highway_iff (k Q : Nat) (w : Point) :
    (exists T, HighwayFrom (spacedObstacles k) T Q w) ↔
      exists m : Nat, Q = spacedPeriod k * m ∧ w = offset (spacedShift k) m := by
  constructor
  · rintro ⟨T, h⟩
    obtain ⟨m, hm⟩ := spacedObstacles_highway_period_dvd k h
    refine ⟨m, hm, ?_⟩
    have h0 := (h (T + 12496) (by omega)).1
    have h1 := ((spacedObstacles_highway k).multiple m (T + 12496) (by omega)).1
    rw [hm] at h0
    have he := h0.symm.trans h1
    simp only [Prod.mk.injEq] at he
    apply Prod.ext <;> omega
  · rintro ⟨m, rfl, rfl⟩
    exact ⟨12496, (spacedObstacles_highway k).multiple m⟩

end LangtonsAnt
