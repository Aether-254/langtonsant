import FreshPhaseRecovery

/-!
# Two more first-visit phases: 6 (quarter turn) and 38 (outside the packed window)

Phase 38's recovery path reaches `x = -79`, outside the packed window `[-64,64)^2`.  The
checker below translates the flipped state into the window first; soundness transports the
result back by translation invariance.

Phase 49 is *not* covered.  Exploration (`scripts/ExploreFreshPhaseRecovery.lean` and longer
runs) shows that for every tested history length `H >= 11` the recovery re-enters at the
same absolute cell `(39,-37)` heading south, with the delay growing by exactly 104 per extra
period and maximal weight `7 > 0`: the ant walks back along the whole highway trail to the
seed's original region.  Such a recovery reads cells outside `x+y <= 0`, so no certificate
of the present history-independent form exists for it.  This is a finite observation only.
-/

namespace LangtonsAnt

def checkShiftedRecovery (f d : Nat) (origin v : Point) : Bool :=
  let F := (flippedAt f).translate v
  decide (weight origin <= 0) && F.black.all (fun p => decide (InBox p)) &&
    checkPackedBounded (weight v) d F.toPacked &&
    checkPackedEntry d F.toPacked (weight origin + weight v)
      (highwaySeed.translate (addPoint v origin))

theorem checkShiftedRecovery_sound {f d : Nat} {origin v : Point}
    (h : checkShiftedRecovery f d origin v = true) : RecoveryCertificate f d origin := by
  simp only [checkShiftedRecovery, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ho, hbox⟩, hb⟩, he⟩ := h
  have hbox' : forall p, p ∈ ((flippedAt f).translate v).black -> InBox p := by
    intro p hp
    exact of_decide_eq_true (List.all_eq_true.mp hbox p hp)
  have hF := ((flippedAt f).translate v).toPacked_toState hbox'
  rw [FiniteState.toState_translate] at hF
  refine ⟨ho, ?_, ?_⟩
  · intro j hj
    have hh := checkPackedBounded_sound hb j hj
    rw [hF, translate_run] at hh
    change weight (addPoint v (run (flippedAt f).toState j).pos) <= _ at hh
    rw [weight_addPoint] at hh
    omega
  · have hh := checkPackedEntry_sound he
    rw [hF, translate_run, FiniteState.toState_translate] at hh
    have ht := hh.translate (negPoint v)
    have hz : addPoint (negPoint v) v = (0, 0) := by
      apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
    have hz' : addPoint (negPoint v) (addPoint v origin) = origin := by
      apply Prod.ext <;> simp [addPoint, negPoint] <;> omega
    have hw : weight origin + weight v + weight (negPoint v) = weight origin := by
      simp [weight, negPoint]; omega
    rw [translate_add, translate_add, hz, hz', translate_zero, hw] at ht
    exact ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_six_check : checkRotatedRecovery (104 * 18 + 6) 12611 .east (-53, -22) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phase_thirty_eight_check :
    checkShiftedRecovery (104 * 13 + 38) 33148 (-77, -25) (20, 20) = true := by
  decide +kernel

theorem phase_thirty_eight_certificate : RecoveryCertificate (104 * 13 + 38) 33148 (-77, -25) :=
  checkShiftedRecovery_sound phase_thirty_eight_check

/-- All first-visit phases except 49 have a history-independent recovery certificate. -/
theorem fresh_phase_recovers_except_49 (phi : Nat) (hphi : phi ∈ freshPhases) (h49 : phi ≠ 49) :
    exists H : Nat, forall s : State, AgreesBelow 0 s highwaySeed.toState -> forall k : Nat,
      EventuallyStandard
        (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos) := by
  by_cases hc : phi ∈ certifiedFreshPhases
  · exact certified_fresh_phase_recovers phi hc
  · have hm : phi ∈ freshPhases.filter (· ∉ certifiedFreshPhases) := by
      simp only [List.mem_filter, hphi, true_and]
      simpa using hc
    rw [uncertifiedFreshPhases] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨18, fun s h k =>
        (checkRotatedRecovery_sound phase_six_check).eventually_shift rfl h k⟩
    · exact ⟨13, fun s h k => phase_thirty_eight_certificate.eventually_shift rfl h k⟩
    · exact absurd rfl h49

end LangtonsAnt
