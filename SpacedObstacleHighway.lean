import InfiniteObstacleHighway

namespace LangtonsAnt

def spacedPoint (k i : Nat) : Point :=
  (-4 - 2 * (((k + 4) * i : Nat) : Int), -4 - 2 * (((k + 4) * i : Nat) : Int))

def spacedShift (k : Nat) : Point := (-8 - 2 * (k : Int), -8 - 2 * (k : Int))

def spacedPeriod (k : Nat) : Nat := 548 + 104 * k

noncomputable def spacedMask (k : Nat) : Board := by
  classical
  exact fun p => decide (exists i : Nat, p = spacedPoint k i)

noncomputable def spacedTail (k : Nat) : Board := fun p => spacedMask k (subPoint p (spacedShift k))

noncomputable def spacedSeed (k : Nat) : State := perturb (spacedMask k) highwaySeed.toState

theorem spacedMask_iff (k : Nat) (p : Point) :
    spacedMask k p = true ↔ exists i : Nat, p = spacedPoint k i := by
  classical
  simp only [spacedMask, decide_eq_true_eq]

theorem spacedPoint_succ (k i : Nat) :
    spacedPoint k (i + 1) = addPoint (spacedShift k) (spacedPoint k i) := by
  apply Prod.ext <;> simp only [spacedPoint, spacedShift, addPoint, Nat.mul_succ, Int.natCast_add] <;> omega

theorem spacedTail_geometry {k : Nat} {p : Point} (h : spacedTail k p = true) :
    p.1 = p.2 ∧ p.1 <= -12 - 2 * (k : Int) ∧ weight p <= -24 - 4 * (k : Int) := by
  obtain ⟨i, hi⟩ := (spacedMask_iff k _).mp h
  simp only [subPoint, spacedPoint, spacedShift, Prod.mk.injEq] at hi
  simp only [weight]
  omega

theorem spacedMask_split (k : Nat) (p : Point) :
    spacedMask k p = true ↔ p = chainHead ∨ spacedTail k p = true := by
  rw [spacedMask_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | zero => exact Or.inl rfl
    | succ i =>
      right
      apply (spacedMask_iff k _).mpr
      refine ⟨i, ?_⟩
      rw [spacedPoint_succ, subPoint_addPoint]
  · intro h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := (spacedMask_iff k _).mp h
      refine ⟨i + 1, ?_⟩
      rw [spacedPoint_succ, ← hi, addPoint_subPoint]

theorem spaced_decompose (k : Nat) (s : State) :
    perturb (spacedMask k) s = perturb (spacedTail k) (flipCell s chainHead) := by
  have hb : (fun p => s.board p ^^ spacedMask k p) =
      fun p => flip s.board chainHead p ^^ spacedTail k p := by
    funext p
    by_cases hp : p = chainHead
    · subst p
      have hm : spacedMask k chainHead = true := (spacedMask_iff k _).mpr ⟨0, rfl⟩
      have ht : spacedTail k chainHead = false := by
        cases hc : spacedTail k chainHead
        · rfl
        · have hh := (spacedTail_geometry hc).2.1
          change (-4 : Int) <= -12 - 2 * (k : Int) at hh
          omega
      rw [hm, ht, flip_same, Bool.xor_false]
      cases s.board chainHead <;> rfl
    · have he : spacedMask k p = spacedTail k p := by
        have hi := spacedMask_split k p
        simp only [hp, false_or] at hi
        cases hm : spacedMask k p <;> cases ht : spacedTail k p <;> simp_all
      rw [flip_other _ hp, he]
  simp only [perturb, flipCell, hb]

theorem spaced_collision_prefix (k n : Nat) (hn : n <= 548) :
    run (spacedSeed k) n = perturb (spacedTail k) (run chainCollisionSeed.toState n) := by
  unfold spacedSeed
  rw [spaced_decompose, ← chainCollisionSeed_toState]
  apply run_perturb_avoids
  intro j hj
  cases hc : spacedTail k (run chainCollisionSeed.toState j).pos
  · rfl
  · have hw := (spacedTail_geometry hc).2.2
    have hb := (chainCollision_range j (by omega)).1
    omega

theorem spaced_collision_entry (k : Nat) :
    AgreesBelow (-16) (run (spacedSeed k) 548)
      (perturb (spacedTail k) (translate chainShift highwaySeed.toState)) := by
  have he := chainCollision_entry.perturb (spacedTail k)
  rw [← spaced_collision_prefix k 548 (by omega)] at he
  exact he

theorem standard_diagonal_lower_bound (n : Nat)
    (hdiag : (run highwaySeed.toState n).pos.1 = (run highwaySeed.toState n).pos.2) :
    -4 - 2 * ((n / 104 : Nat) : Int) < (run highwaySeed.toState n).pos.1 := by
  let q := n / 104
  let j := n % 104
  have hj : j < 104 := Nat.mod_lt n (by decide)
  have hn : 104 * q + j = n := Nat.div_add_mod n 104
  have hp := (highwaySeed_certificate.block_prefix q j (by omega)).pos
  rw [hn] at hp
  change _ = addPoint (offset (-2, -2) q) (run highwaySeed.toState j).pos at hp
  rw [southwest_offset] at hp
  have hc := standard_cycle_diagonal_check ⟨j, hj⟩
  change (highwaySeed.run j).pos.1 = (highwaySeed.run j).pos.2 -> -4 < (highwaySeed.run j).pos.1 at hc
  have he : (highwaySeed.run j).pos = (run highwaySeed.toState j).pos :=
    congrArg State.pos (highwaySeed.toState_run j)
  rw [he] at hc
  rw [hp] at hdiag ⊢
  simp only [addPoint] at hdiag ⊢
  have hh := hc (by omega)
  dsimp [q] at *
  omega

theorem spacedTail_avoids_standard (k n : Nat) (hn : n < 104 * k) :
    spacedTail k (run (translate chainShift highwaySeed.toState) n).pos = false := by
  cases hc : spacedTail k (run (translate chainShift highwaySeed.toState) n).pos
  · rfl
  · have hg := spacedTail_geometry hc
    rw [translate_run] at hg
    change (addPoint chainShift (run highwaySeed.toState n).pos).1 =
        (addPoint chainShift (run highwaySeed.toState n).pos).2 ∧
      (addPoint chainShift (run highwaySeed.toState n).pos).1 <= -12 - 2 * (k : Int) ∧ _ at hg
    simp only [chainShift, addPoint] at hg
    have hd : (run highwaySeed.toState n).pos.1 = (run highwaySeed.toState n).pos.2 := by omega
    have hb := standard_diagonal_lower_bound n hd
    have hq : n / 104 < k := by omega
    omega

theorem spaced_standard_prefix (k n : Nat) (hn : n <= 104 * k) :
    AgreesBelow (-16) (run (spacedSeed k) (548 + n))
      (perturb (spacedTail k) (run (translate chainShift highwaySeed.toState) n)) := by
  have hh := (spaced_collision_entry k).run_perturb n (by
    intro j _
    have hb := (highwaySeed_certificate.translate chainShift).all_bounded j
    exact hb) (fun j hj => spacedTail_avoids_standard k j (by omega))
  rw [← run_add] at hh
  exact hh

set_option maxRecDepth 100000 in
theorem spaced_certificate (k : Nat) :
    HighwayCertificate (spacedSeed k) (spacedPeriod k) (spacedShift k) 0 := by
  refine ⟨by unfold spacedPeriod; omega, by simp [spacedShift, weight]; omega, ?_, ?_⟩
  · intro n hn
    by_cases hfirst : n < 548
    · rw [spaced_collision_prefix k n (by omega)]
      exact (chainCollision_range n hfirst).2
    · have hlen : n - 548 <= 104 * k := by unfold spacedPeriod at hn; omega
      have hp := (spaced_standard_prefix k (n - 548) hlen).pos
      have htime : 548 + (n - 548) = n := by omega
      rw [htime] at hp
      have hb := (highwaySeed_certificate.translate chainShift).all_bounded (n - 548)
      rw [hp]
      change weight (run (translate chainShift highwaySeed.toState) (n - 548)).pos <= 0
      change weight (run (translate chainShift highwaySeed.toState) (n - 548)).pos <= -16 at hb
      omega
  · have hc := highwaySeed_certificate.translate chainShift
    have hm := spaced_standard_prefix k (104 * k) (by omega)
    have he := (hc.blocks k).perturb (spacedTail k)
    have hoff : 0 + weight chainShift + weight (offset (-2, -2) k) = weight (spacedShift k) := by
      rw [southwest_offset]
      simp only [weight, chainShift, spacedShift]
      omega
    rw [hoff] at he
    have hw : weight (spacedShift k) <= -16 := by simp [weight, spacedShift]; omega
    have hh := (hm.weaken hw).trans he
    rw [translate_add] at hh
    have hv : addPoint (offset (-2, -2) k) chainShift = spacedShift k := by
      rw [southwest_offset]
      apply Prod.ext <;> simp [addPoint, chainShift, spacedShift] <;> omega
    rw [hv] at hh
    change AgreesBelow (weight (spacedShift k)) (run (spacedSeed k) (548 + 104 * k))
      (perturb (fun p => spacedMask k (subPoint p (spacedShift k)))
        (translate (spacedShift k) highwaySeed.toState)) at hh
    rw [← perturb_translate] at hh
    simpa only [spacedPeriod, spacedSeed, Int.zero_add] using hh

theorem spaced_highway (k : Nat) : HighwayFrom (spacedSeed k) 0 (548 + 104 * k) (spacedShift k) :=
  (spaced_certificate k).highway

/-- Only the obstacle ray is black initially; the ant starts at the blank state's pose. -/
noncomputable def spacedObstacles (k : Nat) : State :=
  perturb (fun p => spacedMask k (subPoint p chainOrigin)) blank

theorem spacedObstacles_black (k : Nat) (p : Point) :
    (spacedObstacles k).board p = true ↔ exists i : Nat,
      p = (-68 - 2 * (((k + 4) * i : Nat) : Int), -42 - 2 * (((k + 4) * i : Nat) : Int)) := by
  simp only [spacedObstacles, perturb, blank, Bool.false_xor, spacedMask_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Prod.ext <;> simp only [subPoint, chainOrigin, spacedPoint, Prod.mk.injEq] at hi ⊢ <;> omega
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [hi]
    apply Prod.ext <;> simp [subPoint, chainOrigin, spacedPoint] <;> omega

theorem spacedObstacles_avoids_prefix (k j : Nat) (hj : j < 12496) :
    spacedMask k (subPoint (run blank j).pos chainOrigin) = false := by
  cases hm : spacedMask k (subPoint (run blank j).pos chainOrigin)
  · rfl
  · have hp : (spacedObstacles k).board (run blank j).pos = true := by
      simpa only [spacedObstacles, perturb, blank, Bool.false_xor] using hm
    obtain ⟨i, hi⟩ := (spacedObstacles_black k _).mp hp
    by_cases hearly : j < 12080
    · have hb := checkPackedEntry_inBox blank_entry_check j hearly
      rw [packedBlank_toState, hi] at hb
      simp only [InBox] at hb
      omega
    · have htime : j = 12080 + (j - 12080) := by omega
      rw [htime, blank_tail_pos] at hi
      have hp' : (run highwaySeed.toState (j - 12080)).pos =
          addPoint (offset (-2, -2) (5 + (k + 4) * i)) (-2, -2) := by
        rw [southwest_offset]
        apply Prod.ext <;> simp only [addPoint, Int.natCast_add, Prod.mk.injEq] at hi ⊢ <;> omega
      exact False.elim ((phaseFour_first_visit (5 + (k + 4) * i)).2 (j - 12080) (by omega) hp')

theorem spacedObstacles_entry (k : Nat) :
    AgreesBelow (-102) (run (spacedObstacles k) 12496) (translate chainOrigin (spacedSeed k)) := by
  have hp := run_perturb_avoids (fun p => spacedMask k (subPoint p chainOrigin))
    blank 12496 (spacedObstacles_avoids_prefix k)
  have hh := blank_chain_entry.perturb (fun p => spacedMask k (subPoint p chainOrigin))
  rw [← hp, ← perturb_translate] at hh
  exact hh

theorem spacedObstacles_highway (k : Nat) :
    HighwayFrom (spacedObstacles k) 12496 (spacedPeriod k) (spacedShift k) :=
  ((spaced_certificate k).translate chainOrigin).highway_of_entry (spacedObstacles_entry k)

theorem spacedObstacles_reads (k n : Nat) :
    readColor (spacedObstacles k) (12496 + n) = readColor (spacedSeed k) (n % spacedPeriod k) := by
  have hc := (spaced_certificate k).translate chainOrigin
  have he : AgreesBelow (0 + weight chainOrigin) (run (spacedObstacles k) 12496)
      (translate chainOrigin (spacedSeed k)) := spacedObstacles_entry k
  have hh := hc.reads_of_matches he n
  rw [translate_readColor] at hh
  simpa only [readColor, ← run_add] using hh

theorem spacedObstacles_not_finite (k : Nat) : ¬FiniteSupport (spacedObstacles k).board := by
  rintro ⟨cells, hc⟩
  let i := (-(weightFloor cells)).toNat + 1
  let p : Point := (-68 - 2 * (((k + 4) * i : Nat) : Int), -42 - 2 * (((k + 4) * i : Nat) : Int))
  have hp := (spacedObstacles_black k p).mpr ⟨i, rfl⟩
  have hw := weightFloor_le (hc p hp)
  have hi := Int.mul_le_mul_of_nonneg_right (show (1 : Int) <= (k : Int) + 4 by omega)
    (show (0 : Int) <= (i : Int) by omega)
  simp only [Int.one_mul] at hi
  dsimp [p, weight] at hw
  have hlow : weightFloor cells <= -110 - 4 * (i : Int) := by omega
  dsimp [i] at hlow
  omega

theorem spacedPeriod_drift_balance (k : Nat) :
    (spacedPeriod k : Int) + 52 * (spacedShift k).1 = 132 := by
  simp only [spacedPeriod, spacedShift, Int.natCast_add, Int.natCast_mul]
  omega

/-- Different spacings have different average velocities, irrespective of phase or starting time. -/
theorem spaced_speeds_injective {k l : Nat}
    (h : (spacedPeriod l : Int) * (spacedShift k).1 =
      (spacedPeriod k : Int) * (spacedShift l).1) : k = l := by
  have hk := spacedPeriod_drift_balance k
  have hl := spacedPeriod_drift_balance l
  have he : (spacedPeriod l : Int) * 132 = (spacedPeriod k : Int) * 132 := by
    calc
      (spacedPeriod l : Int) * 132 =
          (spacedPeriod l : Int) * ((spacedPeriod k : Int) + 52 * (spacedShift k).1) := by rw [hk]
      _ = (spacedPeriod l : Int) * (spacedPeriod k : Int) +
          52 * ((spacedPeriod l : Int) * (spacedShift k).1) := by
        rw [Int.mul_add]
        congr 1
        ac_rfl
      _ = (spacedPeriod k : Int) * (spacedPeriod l : Int) +
          52 * ((spacedPeriod k : Int) * (spacedShift l).1) := by rw [h, Int.mul_comm (spacedPeriod l : Int)]
      _ = (spacedPeriod k : Int) * ((spacedPeriod l : Int) + 52 * (spacedShift l).1) := by
        rw [Int.mul_add]
        congr 1
        ac_rfl
      _ = (spacedPeriod k : Int) * 132 := by rw [hl]
  simp only [spacedPeriod, Int.natCast_add, Int.natCast_mul] at he
  omega

theorem spacedObstacles_no_other_spacing {k l T : Nat} (hkl : k ≠ l) :
    ¬HighwayFrom (spacedObstacles k) T (spacedPeriod l) (spacedShift l) := by
  intro h
  exact hkl (spaced_speeds_injective (highway_horizontal_speeds_compatible (spacedObstacles_highway k) h))

theorem spacedObstacles_no_period104 (k T : Nat) (v : Point) :
    ¬HighwayFrom (spacedObstacles k) T 104 v := by
  intro h
  have he := highway_horizontal_speeds_compatible (spacedObstacles_highway k) h
  have hP : (0 : Int) <= (spacedPeriod k : Int) := by omega
  by_cases hv : -1 <= v.1
  · have hh := Int.mul_le_mul_of_nonneg_left hv hP
    simp only [spacedPeriod, spacedShift, Int.natCast_add, Int.natCast_mul] at he hh
    omega
  · have hh := Int.mul_le_mul_of_nonneg_left (show v.1 <= -2 by omega) hP
    simp only [spacedPeriod, spacedShift, Int.natCast_add, Int.natCast_mul] at he hh
    omega

theorem spacedObstacles_not_eventuallyStandard (k : Nat) : ¬EventuallyStandard (spacedObstacles k) := by
  rintro ⟨T, v, _, h⟩
  exact spacedObstacles_no_period104 k T v h.1

/-- Every eventual positive period is at least the certified period divided by 132. -/
theorem spacedObstacles_period_lower_bound (k : Nat) {T Q : Nat} {w : Point}
    (hQ : 0 < Q) (h : HighwayFrom (spacedObstacles k) T Q w) : spacedPeriod k <= 132 * Q := by
  have he := highway_horizontal_speeds_compatible (spacedObstacles_highway k) h
  have hP : (0 : Int) <= (spacedPeriod k : Int) := by omega
  have hb : (spacedPeriod k : Int) * ((Q : Int) + 52 * w.1) = 132 * (Q : Int) := by
    calc
      (spacedPeriod k : Int) * ((Q : Int) + 52 * w.1) =
          (Q : Int) * (spacedPeriod k : Int) + 52 * ((spacedPeriod k : Int) * w.1) := by
        rw [Int.mul_add]
        congr 1 <;> ac_rfl
      _ = (Q : Int) * (spacedPeriod k : Int) + 52 * ((Q : Int) * (spacedShift k).1) := by rw [he]
      _ = (Q : Int) * ((spacedPeriod k : Int) + 52 * (spacedShift k).1) := by
        rw [Int.mul_add]
        congr 1
        ac_rfl
      _ = (Q : Int) * 132 := by rw [spacedPeriod_drift_balance]
      _ = 132 * (Q : Int) := Int.mul_comm _ _
  have hc : (1 : Int) <= (Q : Int) + 52 * w.1 := by
    by_cases hh : (Q : Int) + 52 * w.1 <= 0
    · have hz := Int.mul_le_mul_of_nonneg_left hh hP
      omega
    · omega
  have hl := Int.mul_le_mul_of_nonneg_left hc hP
  omega

/-- Positive eventual periods have no common bound across these infinite-support states. -/
theorem spacedObstacles_unbounded_periods (B : Nat) :
    HighwayFrom (spacedObstacles (2 * B)) 12496 (spacedPeriod (2 * B)) (spacedShift (2 * B)) ∧
      forall T Q w, 0 < Q -> Q <= B -> ¬HighwayFrom (spacedObstacles (2 * B)) T Q w := by
  refine ⟨spacedObstacles_highway (2 * B), ?_⟩
  intro T Q w hQ hB h
  have hb := spacedObstacles_period_lower_bound (2 * B) hQ h
  simp only [spacedPeriod] at hb
  omega

theorem spacedMask_zero : spacedMask 0 = infiniteChainMask := by
  funext p
  have hi := spacedMask_iff 0 p
  have hj := infiniteChainMask_iff p
  have hp : forall i, spacedPoint 0 i = chainPoint i := by
    intro i
    apply Prod.ext <;> simp [spacedPoint, chainPoint] <;> omega
  simp only [hp] at hi
  cases hs : spacedMask 0 p <;> cases ht : infiniteChainMask p <;> simp_all

theorem spacedObstacles_zero : spacedObstacles 0 = infiniteObstacles := by
  simp only [spacedObstacles, infiniteObstacles, spacedMask_zero]

end LangtonsAnt
