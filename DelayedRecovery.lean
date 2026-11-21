import FreshCollision

namespace LangtonsAnt

/-- A ray of single black cells, each first encountered in phase four of the blank highway. -/
def delayedObstacle (k : Nat) : Point := (-66 - 2 * (k : Int), -40 - 2 * (k : Int))

def delayedContactTime (k : Nat) : Nat := 12500 + 104 * k

theorem blank_entryAt : EntryAt blank 12080 .north (-56, -30) := by
  have hb : AgreesBelow (weight (-56, -30)) (run blank 12080)
      (translate (-56, -30) highwaySeed.toState) := blank_entry
  have hh := hb.normalize_translate
  have hr (s : State) : rotateState .north s = s := by cases s; rfl
  simpa only [EntryAt, normalize, inverseRotation, hr] using hh

theorem blank_tail_pos (n : Nat) :
    (run blank (12080 + n)).pos = addPoint (-56, -30) (run highwaySeed.toState n).pos := by
  have hc := highwaySeed_certificate.translate (-56, -30)
  have he : AgreesBelow (0 + weight (-56, -30)) (run blank 12080)
      (translate (-56, -30) highwaySeed.toState) := blank_entry
  have hm := hc.matches_forever he n
  rw [← run_add, translate_run] at hm
  exact hm.pos

theorem delayedObstacle_first_visit (k : Nat) :
    (run blank (delayedContactTime k)).pos = delayedObstacle k ∧
    forall n, n < delayedContactTime k -> (run blank n).pos ≠ delayedObstacle k := by
  have ht : delayedContactTime k = 12080 + (104 * (k + 4) + 4) := by
    unfold delayedContactTime
    omega
  have hp : delayedObstacle k =
      addPoint (-56, -30) (addPoint (offset (-2, -2) (k + 4)) (-2, -2)) := by
    rw [southwest_offset]
    apply Prod.ext <;> simp [delayedObstacle, addPoint] <;> omega
  have hv := phaseFour_first_visit (k + 4)
  constructor
  · rw [ht, blank_tail_pos, hv.1, hp]
  · intro n hn he
    by_cases hearly : n < 12080
    · have hb := checkPackedEntry_inBox blank_entry_check n hearly
      rw [packedBlank_toState, he] at hb
      simp only [InBox, delayedObstacle] at hb
      omega
    · have hn' : n = 12080 + (n - 12080) := by omega
      rw [hn', blank_tail_pos, hp] at he
      have hpos : (run highwaySeed.toState (n - 12080)).pos =
          addPoint (offset (-2, -2) (k + 4)) (-2, -2) := by
        apply Prod.ext <;> simp only [addPoint, Prod.mk.injEq] at he ⊢ <;> omega
      exact hv.2 (n - 12080) (by omega) hpos

theorem singleBlack_eq_perturb (p : Point) :
    singleBlack p = perturb (fun q => decide (q = p)) blank := by
  simp [singleBlack, perturb, blank]

theorem delayedObstacle_contact_state (k : Nat) :
    run (singleBlack (delayedObstacle k)) (delayedContactTime k) =
      flipCell (run blank (delayedContactTime k)) (run blank (delayedContactTime k)).pos := by
  have hv := delayedObstacle_first_visit k
  have hf : FirstContact (fun q => decide (q = delayedObstacle k)) blank (delayedContactTime k) := by
    refine ⟨by simp [hv.1], ?_⟩
    intro j hj
    simp [hv.2 j hj]
  rw [singleBlack_eq_perturb, firstContact_state hf, flipCell_eq_perturb, hv.1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- These arbitrarily distant, genuinely encountered one-cell obstacles all recover. -/
theorem delayedObstacle_standard (k : Nat) :
    StandardHighwayFrom (singleBlack (delayedObstacle k)) (12940 + 104 * k) (-2, -2) := by
  have hsum : delayedContactTime k + 440 = 12940 + 104 * k := by
    unfold delayedContactTime
    omega
  have ht : 12080 + (104 * (k + 4) + 4) = delayedContactTime k := by
    unfold delayedContactTime
    omega
  have hr := blank_entryAt.flip_recovers_at_phase_four (k + 4)
  rw [ht, ← delayedObstacle_contact_state] at hr
  have hh := hr.of_run
  simpa only [hsum, rotatePoint] using hh

theorem singleBlack_no_highway_before_late_contact {p : Point} {t T : Nat}
    (ht : (run blank t).pos = p)
    (hfirst : forall j, j < t -> (run blank j).pos ≠ p)
    (hlate : 12184 <= t) (hT : T + 104 <= t) :
    forall v, ¬HighwayFrom (singleBlack p) T 104 v := by
  have hcollision := singleBlack_first_collision ht hfirst
  intro v hhighway
  have hnt : t - 104 + 104 = t := by omega
  have hactual := hhighway.reads_periodic (n := t - 104) (by omega)
  have hblank := blank_highway.reads_periodic (n := t - 104) (by omega)
  rw [hnt] at hactual hblank
  rw [hcollision.1, hcollision.2.2 (t - 104) (by omega)] at hactual
  rw [hcollision.2.1] at hblank
  exact Bool.noConfusion (hactual.trans hblank.symm)

/-- Unbounded highway delay persists even within an explicitly proved recovering family. -/
theorem one_black_unbounded_delay_with_recovery (N : Nat) :
    exists p : Point, EventuallyStandard (singleBlack p) ∧
      forall T, T <= N -> forall v, ¬HighwayFrom (singleBlack p) T 104 v := by
  refine ⟨delayedObstacle N,
    ⟨12940 + 104 * N, (-2, -2), diagonal_rotated_southwest .north, delayedObstacle_standard N⟩, ?_⟩
  intro T hT
  have hv := delayedObstacle_first_visit N
  apply singleBlack_no_highway_before_late_contact hv.1 hv.2
  · unfold delayedContactTime
    omega
  · unfold delayedContactTime
    omega

end LangtonsAnt
