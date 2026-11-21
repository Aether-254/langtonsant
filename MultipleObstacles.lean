import ObstacleChain

namespace LangtonsAnt

def chainOrigin : Point := (-64, -38)

def initialChainMask (n : Nat) : Board := fun p => chainMask n (subPoint p chainOrigin)

/-- All n black cells are installed at time zero on an otherwise blank board. -/
def multipleObstacles (n : Nat) : State := perturb (initialChainMask n) blank

theorem multipleObstacles_black (n : Nat) (p : Point) :
    (multipleObstacles n).board p = true ↔
      exists i, i < n ∧ p = (-68 - 8 * (i : Int), -42 - 8 * (i : Int)) := by
  simp only [multipleObstacles, perturb, blank, Bool.false_xor, initialChainMask, chainMask,
    decide_eq_true_eq, chainCells_mem]
  constructor
  · rintro ⟨i, hi, hp⟩
    refine ⟨i, hi, ?_⟩
    apply Prod.ext <;> simp only [subPoint, chainOrigin, chainPoint, Prod.mk.injEq] at hp ⊢ <;> omega
  · rintro ⟨i, hi, hp⟩
    refine ⟨i, hi, ?_⟩
    rw [hp]
    apply Prod.ext <;> simp [subPoint, chainOrigin, chainPoint] <;> omega

theorem multipleObstacles_finite (n : Nat) : FiniteSupport (multipleObstacles n).board := by
  refine ⟨(List.range n).map (fun (i : Nat) => (-68 - 8 * (i : Int), -42 - 8 * (i : Int))), ?_⟩
  intro p hp
  obtain ⟨i, hi, he⟩ := (multipleObstacles_black n p).mp hp
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, he.symm⟩

theorem blank_chain_entry :
    AgreesBelow (-102) (run blank 12496) (translate chainOrigin highwaySeed.toState) := by
  have hc := highwaySeed_certificate.translate (-56, -30)
  have he : AgreesBelow (0 + weight (-56, -30)) (run blank 12080)
      (translate (-56, -30) highwaySeed.toState) := blank_entry
  have hm := hc.matches_forever he 416
  have hb := hc.blocks 4
  have hp : offset (-2, -2) 4 = (-8, -8) := by decide
  rw [hp, translate_add] at hb
  have h0 : addPoint (-8, -8) (-56, -30) = chainOrigin := by decide
  rw [h0] at hb
  have hweak : AgreesBelow (-102) (run (run blank 12080) 416)
      (run (translate (-56, -30) highwaySeed.toState) 416) := hm.weaken (by decide)
  have hh := hweak.trans hb
  rw [← run_add] at hh
  exact hh

theorem initialChain_avoids_prefix (n : Nat) (j : Nat) (hj : j < 12496) :
    initialChainMask n (run blank j).pos = false := by
  cases hm : initialChainMask n (run blank j).pos
  · rfl
  · have hp : (multipleObstacles n).board (run blank j).pos = true := by
      simpa only [multipleObstacles, perturb, blank, Bool.false_xor] using hm
    obtain ⟨i, _, hi⟩ := (multipleObstacles_black n _).mp hp
    by_cases hearly : j < 12080
    · have hb := checkPackedEntry_inBox blank_entry_check j hearly
      rw [packedBlank_toState, hi] at hb
      simp only [InBox] at hb
      omega
    · have htime : j = 12080 + (j - 12080) := by omega
      rw [htime, blank_tail_pos] at hi
      have hp' : (run highwaySeed.toState (j - 12080)).pos =
          addPoint (offset (-2, -2) (5 + 4 * i)) (-2, -2) := by
        rw [southwest_offset]
        apply Prod.ext <;> simp only [addPoint, Prod.mk.injEq] at hi ⊢ <;> omega
      exact False.elim ((phaseFour_first_visit (5 + 4 * i)).2 (j - 12080) (by omega) hp')

theorem multipleObstacles_entry (n : Nat) :
    AgreesBelow 0 (translate (64, 38) (run (multipleObstacles n) 12496))
      (perturb (chainMask n) highwaySeed.toState) := by
  have hp := run_perturb_avoids (initialChainMask n) blank 12496 (initialChain_avoids_prefix n)
  change run (multipleObstacles n) 12496 = _ at hp
  have hh := blank_chain_entry.perturb (initialChainMask n)
  rw [← hp] at hh
  have ht := hh.translate (64, 38)
  have hmask : (fun p => initialChainMask n (subPoint p (64, 38))) = chainMask n := by
    funext p
    have he : subPoint (subPoint p (64, 38)) chainOrigin = p := by
      apply Prod.ext <;> simp [subPoint, chainOrigin] <;> omega
    simp only [initialChainMask, he]
  rw [perturb_translate, translate_add, hmask] at ht
  have hz : addPoint (64, 38) chainOrigin = (0, 0) := by decide
  rw [hz, translate_zero] at ht
  exact ht

/-- A fixed finite list of arbitrarily many encountered obstacles, with a proved linear recovery bound. -/
theorem multipleObstacles_standard (n : Nat) :
    StandardHighwayFrom (multipleObstacles n) (12496 + 548 * n) (-2, -2) := by
  have hs := chain_standard n (multipleObstacles_entry n)
  have ht := hs.translate (-64, -38)
  rw [translate_add] at ht
  have hz : addPoint (-64, -38) (64, 38) = (0, 0) := by decide
  rw [hz, translate_zero] at ht
  exact ht.of_run

theorem multipleObstacles_visits (n i : Nat) (hi : i < n) :
    (run (multipleObstacles n) (12604 + 548 * i)).pos =
      (-68 - 8 * (i : Int), -42 - 8 * (i : Int)) := by
  have hh := chain_visits n (multipleObstacles_entry n) i hi
  rw [translate_run, ← run_add] at hh
  change addPoint (64, 38) (run (multipleObstacles n) (12496 + (548 * i + 108))).pos = chainPoint i at hh
  have ht : 12496 + (548 * i + 108) = 12604 + 548 * i := by omega
  rw [ht] at hh
  apply Prod.ext <;> simp only [addPoint, chainPoint, Prod.mk.injEq] at hh ⊢ <;> omega

theorem multipleObstacles_first_visits (n i : Nat) (hi : i < n) :
    forall j, j < 12604 + 548 * i ->
      (run (multipleObstacles n) j).pos ≠ (-68 - 8 * (i : Int), -42 - 8 * (i : Int)) := by
  intro j hj he
  by_cases hearly : j < 12496
  · have hr := run_perturb_avoids (initialChainMask n) blank j
      (fun m hm => initialChain_avoids_prefix n m (by omega))
    have hp : (run (multipleObstacles n) j).pos = (run blank j).pos := by
      change (run (perturb (initialChainMask n) blank) j).pos = _
      rw [hr]
      rfl
    have hw := initialChain_avoids_prefix n j hearly
    have hb : (multipleObstacles n).board (run blank j).pos = true := by
      apply (multipleObstacles_black n _).mpr
      exact ⟨i, hi, hp.symm.trans he⟩
    simp only [multipleObstacles, perturb, blank, Bool.false_xor] at hb
    change initialChainMask n (run blank j).pos = true at hb
    rw [hw] at hb
    contradiction
  · have hh := chain_first_visits n (multipleObstacles_entry n) i hi (j - 12496) (by omega)
    apply hh
    rw [translate_run, ← run_add]
    have ht : 12496 + (j - 12496) = j := by omega
    rw [ht]
    change addPoint (64, 38) (run (multipleObstacles n) j).pos = chainPoint i
    rw [he]
    apply Prod.ext <;> simp [addPoint, chainPoint] <;> omega

end LangtonsAnt
