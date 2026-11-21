import SpacedHighwayClassification

namespace LangtonsAnt

/-- Obstacles lie on the even southwest diagonal at or beyond the next head. -/
def AheadMask (mask : Board) : Prop :=
  forall p, mask p = true -> exists i : Nat, p = (-4 - 2 * (i : Int), -4 - 2 * (i : Int))

def shiftedObstacles (k : Nat) (mask : Board) : Board :=
  fun p => mask (subPoint p (spacedShift k))

def prependObstacles (k : Nat) (mask : Board) : Board :=
  fun p => decide (p = chainHead) || shiftedObstacles k mask p

theorem shiftedObstacles_geometry {mask : Board} (ha : AheadMask mask) (k : Nat) {p : Point}
    (h : shiftedObstacles k mask p = true) :
    p.1 = p.2 ∧ p.1 <= -12 - 2 * (k : Int) ∧ weight p <= -24 - 4 * (k : Int) := by
  obtain ⟨i, hi⟩ := ha _ h
  simp only [subPoint, spacedShift, Prod.mk.injEq] at hi
  simp only [weight]
  omega

theorem prependObstacles_ahead {mask : Board} (ha : AheadMask mask) (k : Nat) :
    AheadMask (prependObstacles k mask) := by
  intro p hp
  simp only [prependObstacles, Bool.or_eq_true, decide_eq_true_eq] at hp
  rcases hp with hp | hp
  · exact ⟨0, hp⟩
  · obtain ⟨i, hi⟩ := ha _ hp
    refine ⟨k + 4 + i, ?_⟩
    apply Prod.ext <;> simp only [subPoint, spacedShift, Prod.mk.injEq, Int.natCast_add] at hi ⊢ <;> omega

theorem prependObstacles_decompose {mask : Board} (ha : AheadMask mask) (k : Nat) (s : State) :
    perturb (prependObstacles k mask) s = perturb (shiftedObstacles k mask) (flipCell s chainHead) := by
  have hb : (fun p => s.board p ^^ prependObstacles k mask p) =
      fun p => flip s.board chainHead p ^^ shiftedObstacles k mask p := by
    funext p
    by_cases hp : p = chainHead
    · subst p
      have ht : shiftedObstacles k mask chainHead = false := by
        cases hc : shiftedObstacles k mask chainHead
        · rfl
        · have hh := (shiftedObstacles_geometry ha k hc).2.1
          change (-4 : Int) <= -12 - 2 * (k : Int) at hh
          omega
      simp only [prependObstacles, decide_true, Bool.true_or, ht, Bool.xor_false, flip_same]
      cases s.board chainHead <;> rfl
    · simp only [prependObstacles, hp, decide_false, Bool.false_or, flip_other _ hp]
  simp only [perturb, flipCell, hb]

theorem shiftedObstacles_avoid_collision {mask : Board} (ha : AheadMask mask) (k j : Nat) (hj : j < 548) :
    shiftedObstacles k mask (run chainCollisionSeed.toState j).pos = false := by
  cases hc : shiftedObstacles k mask (run chainCollisionSeed.toState j).pos
  · rfl
  · have hw := (shiftedObstacles_geometry ha k hc).2.2
    have hb := (chainCollision_range j hj).1
    omega

theorem shiftedObstacles_avoid_standard {mask : Board} (ha : AheadMask mask) (k j : Nat) (hj : j < 104 * k) :
    shiftedObstacles k mask (run (translate chainShift highwaySeed.toState) j).pos = false := by
  cases hc : shiftedObstacles k mask (run (translate chainShift highwaySeed.toState) j).pos
  · rfl
  · have hg := shiftedObstacles_geometry ha k hc
    rw [translate_run] at hg
    change (addPoint chainShift (run highwaySeed.toState j).pos).1 =
        (addPoint chainShift (run highwaySeed.toState j).pos).2 ∧
      (addPoint chainShift (run highwaySeed.toState j).pos).1 <= -12 - 2 * (k : Int) ∧ _ at hg
    simp only [chainShift, addPoint] at hg
    have hd : (run highwaySeed.toState j).pos.1 = (run highwaySeed.toState j).pos.2 := by omega
    have hb := standard_diagonal_lower_bound j hd
    have hq : j / 104 < k := by omega
    omega

theorem variableBlock_collision_prefix {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState)) (n : Nat) (hn : n <= 548) :
    AgreesBelow 0 (run s n) (perturb (shiftedObstacles k mask) (run chainCollisionSeed.toState n)) := by
  rw [prependObstacles_decompose ha, ← chainCollisionSeed_toState] at h
  exact h.run_perturb n (fun j hj => (chainCollision_range j (by omega)).2)
    (fun j hj => shiftedObstacles_avoid_collision ha k j (by omega))

theorem variableBlock_standard_prefix {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState))
    (n : Nat) (hn : n <= 104 * k) :
    AgreesBelow (-16) (run s (548 + n))
      (perturb (shiftedObstacles k mask) (run (translate chainShift highwaySeed.toState) n)) := by
  have hr := variableBlock_collision_prefix ha k h 548 (by decide)
  have he := chainCollision_entry.perturb (shiftedObstacles k mask)
  have hh := (hr.weaken (by decide : (-16 : Int) <= 0)).trans he
  have hm := hh.run_perturb n
    (fun j _ => (highwaySeed_certificate.translate chainShift).all_bounded j)
    (fun j hj => shiftedObstacles_avoid_standard ha k j (by omega))
  rw [← run_add] at hm
  exact hm

theorem variableBlock_entry {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState)) :
    AgreesBelow (weight (spacedShift k)) (run s (spacedPeriod k))
      (translate (spacedShift k) (perturb mask highwaySeed.toState)) := by
  have hm := variableBlock_standard_prefix ha k h (104 * k) (by omega)
  have he := ((highwaySeed_certificate.translate chainShift).blocks k).perturb (shiftedObstacles k mask)
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
  change AgreesBelow (weight (spacedShift k)) (run s (548 + 104 * k))
    (perturb (fun p => mask (subPoint p (spacedShift k)))
      (translate (spacedShift k) highwaySeed.toState)) at hh
  rw [← perturb_translate] at hh
  exact hh

theorem variableBlock_step {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState)) :
    AgreesBelow 0 (translate (subPoint (0, 0) (spacedShift k)) (run s (spacedPeriod k)))
      (perturb mask highwaySeed.toState) := by
  have hh := (variableBlock_entry ha k h).translate (subPoint (0, 0) (spacedShift k))
  rw [translate_add] at hh
  have hz : addPoint (subPoint (0, 0) (spacedShift k)) (spacedShift k) = (0, 0) := by
    apply Prod.ext <;> simp [addPoint, subPoint] <;> omega
  have hw : weight (spacedShift k) + weight (subPoint (0, 0) (spacedShift k)) = 0 := by
    simp [weight, subPoint]; omega
  rw [hz, translate_zero, hw] at hh
  exact hh

theorem aheadMask_avoids_blank_prefix {mask : Board} (ha : AheadMask mask) (j : Nat) (hj : j < 12496) :
    mask (subPoint (run blank j).pos chainOrigin) = false := by
  cases hm : mask (subPoint (run blank j).pos chainOrigin)
  · rfl
  · obtain ⟨i, hi⟩ := ha _ hm
    have hp : (run blank j).pos = (-68 - 2 * (i : Int), -42 - 2 * (i : Int)) := by
      apply Prod.ext <;> simp only [subPoint, chainOrigin, Prod.mk.injEq] at hi ⊢ <;> omega
    by_cases hearly : j < 12080
    · have hb := checkPackedEntry_inBox blank_entry_check j hearly
      rw [packedBlank_toState, hp] at hb
      simp only [InBox] at hb
      omega
    · have htime : j = 12080 + (j - 12080) := by omega
      rw [htime, blank_tail_pos] at hp
      have hp' : (run highwaySeed.toState (j - 12080)).pos =
          addPoint (offset (-2, -2) (5 + i)) (-2, -2) := by
        rw [southwest_offset]
        apply Prod.ext <;> simp only [addPoint, Int.natCast_add, Prod.mk.injEq] at hp ⊢ <;> omega
      exact False.elim ((phaseFour_first_visit (5 + i)).2 (j - 12080) (by omega) hp')

theorem aheadMask_blank_entry {mask : Board} (ha : AheadMask mask) :
    AgreesBelow (-102) (run (perturb (fun p => mask (subPoint p chainOrigin)) blank) 12496)
      (translate chainOrigin (perturb mask highwaySeed.toState)) := by
  have hp := run_perturb_avoids (fun p => mask (subPoint p chainOrigin)) blank 12496
    (aheadMask_avoids_blank_prefix ha)
  have hh := blank_chain_entry.perturb (fun p => mask (subPoint p chainOrigin))
  rw [← hp, ← perturb_translate] at hh
  exact hh

theorem AgreesBelow.unshift {s t : State} {v : Point}
    (h : AgreesBelow (weight v) s (LangtonsAnt.translate v t)) :
    AgreesBelow 0 (LangtonsAnt.translate (subPoint (0, 0) v) s) t := by
  have hh := h.translate (subPoint (0, 0) v)
  rw [translate_add] at hh
  have hz : addPoint (subPoint (0, 0) v) v = (0, 0) := by
    apply Prod.ext <;> simp [addPoint, subPoint] <;> omega
  have hw : weight v + weight (subPoint (0, 0) v) = 0 := by simp [weight, subPoint]; omega
  rw [hz, translate_zero, hw] at hh
  exact hh

theorem variableBlock_entry_translated {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State} (v : Point)
    (h : AgreesBelow (weight v) s (translate v (perturb (prependObstacles k mask) highwaySeed.toState))) :
    AgreesBelow (weight (addPoint v (spacedShift k))) (run s (spacedPeriod k))
      (translate (addPoint v (spacedShift k)) (perturb mask highwaySeed.toState)) := by
  have hh := (variableBlock_entry ha k h.unshift).translate v
  rw [translate_run, translate_add, addPoint_subPoint, translate_zero, translate_add] at hh
  simpa only [weight_addPoint, Int.add_comm] using hh

set_option maxRecDepth 100000 in
theorem variableBlock_collision_reads {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState)) (n : Nat) (hn : n < 548) :
    readColor s n = obstacleColor n := by
  have hm := variableBlock_collision_prefix ha k h n (by omega)
  have he : readColor s n = readColor chainCollisionSeed.toState n := by
    unfold readColor
    rw [hm.pos]
    have hc := hm.board (run chainCollisionSeed.toState n).pos (chainCollision_range n hn).2
    simpa only [perturb, shiftedObstacles_avoid_collision ha k n hn, Bool.xor_false] using hc
  rw [he]
  symm
  simpa only [obstacleColor, obstacleWord, Nat.mod_eq_of_lt hn, List.getElem?_toArray] using
    finiteReadWord_get chainCollisionSeed 548 n hn

set_option maxRecDepth 100000 in
theorem variableBlock_standard_reads {mask : Board} (ha : AheadMask mask) (k : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (prependObstacles k mask) highwaySeed.toState)) (n : Nat) (hn : n < 104 * k) :
    readColor s (548 + n) = certifiedColor n := by
  have hm := variableBlock_standard_prefix ha k h n (by omega)
  have hb := (highwaySeed_certificate.translate chainShift).all_bounded n
  have he : readColor s (548 + n) = readColor (translate chainShift highwaySeed.toState) n := by
    unfold readColor
    rw [hm.pos]
    have hc := hm.board (run (translate chainShift highwaySeed.toState) n).pos hb
    simpa only [perturb, shiftedObstacles_avoid_standard ha k n hn, Bool.xor_false] using hc
  rw [he, translate_readColor, highwaySeed_exact_reads]

end LangtonsAnt
