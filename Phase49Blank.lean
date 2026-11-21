import Phase49K3

namespace LangtonsAnt

theorem Y49Frame_toState : Y49Frame.toWide.toState = rotateState .west
    (LangtonsAnt.translate (-56, -30) Y49) := by
  rw [FiniteState.toWide_toState _ (fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp y49_frame_inWide_check p hp))]
  rw [Y49Frame, FiniteState.toState_rotate, FiniteState.toState_translate, Y49FS_toState]

theorem y49_frame_pos (n : Nat) :
    (run Y49 n).pos = subPoint (rotatePoint .east (run Y49Frame.toWide.toState n).pos) (-56, -30) := by
  rw [Y49Frame_toState, rotate_run, translate_run]
  simp only [rotateState, LangtonsAnt.translate]
  apply Prod.ext <;> simp [rotatePoint, addPoint, subPoint] <;> omega

theorem y49_standard : StandardHighwayFrom Y49 y49Delay (rotatePoint .east (-2, -2)) := by
  have he0 := (checkWideGuardEntry_sound y49_run_check).2
  rw [FiniteState.toState_translate] at he0
  have he : AgreesBelow (weight ((-30, -15) : Point)) (run Y49Frame.toWide.toState y49Delay)
      (LangtonsAnt.translate (-30, -15) highwaySeed.toState) := he0
  have hs := standard_highway_of_entry (-30, -15) he
  have hr := (hs.rotate .east).translate (56, 30)
  rw [Y49Frame_toState] at hr
  have hinv : rotateState .east (rotateState .west (LangtonsAnt.translate (-56, -30) Y49)) =
      LangtonsAnt.translate (-56, -30) Y49 := inverse_rotateState .east _
  rw [hinv, translate_add] at hr
  have hz : addPoint ((56, 30) : Point) (-56, -30) = (0, 0) := by decide
  rw [hz, translate_zero] at hr
  exact hr

theorem y49_all_U (n : Nat) : U49 (run Y49 n).pos := by
  rw [y49_frame_pos]
  by_cases hn : n < y49Delay
  · have hg := of_decide_eq_true ((checkWideGuardEntry_sound y49_run_check).1 n hn)
    simp only [U49, weight, subPoint, rotatePoint] at hg ⊢
    omega
  · obtain ⟨m, rfl⟩ : exists m, n = y49Delay + m := ⟨n - y49Delay, by omega⟩
    have hc := highwaySeed_certificate.translate (-30, -15)
    have he : AgreesBelow (0 + weight ((-30, -15) : Point)) (run Y49Frame.toWide.toState y49Delay)
        (LangtonsAnt.translate (-30, -15) highwaySeed.toState) := by
      have h0 := (checkWideGuardEntry_sound y49_run_check).2
      rw [FiniteState.toState_translate] at h0
      exact h0
    have hm := hc.matches_forever he m
    rw [← run_add, translate_run] at hm
    rw [hm.pos]
    have hs := trail_seed_run_strip m
    simp only [TrailStrip, trailCross] at hs
    simp only [U49, weight, subPoint, rotatePoint, LangtonsAnt.translate, addPoint]
    omega

/-! ## 7. Conclusion -/

theorem flip49_blank_standard (k : Nat) : EventuallyStandard (flip49 blankEntryState k) := by
  have hh := y49_standard.of_regionAgree (flip49_blank_U k) y49_all_U
  exact ⟨align49 k + y49Delay, rotatePoint .east (-2, -2), diagonal_rotated_southwest .east,
    hh.of_run⟩

/-- Single black cells first reached by the blank orbit at phase 49, at least 13 periods after
the blank entry. -/
theorem singleBlack_phase49 {q : Point} {tau : Nat}
    (hc : FirstContact (fun x => decide (x = q)) blank tau)
    (hlate : 12080 + 104 * 13 + 49 <= tau) (h49 : (tau - 12080) % 104 = 49) :
    EventuallyStandard (singleBlack q) := by
  obtain ⟨k, rfl⟩ : exists k, tau = 12080 + phase49Time k := by
    refine ⟨(tau - 12080 - 1401) / 104, ?_⟩
    unfold phase49Time trailFlipTime
    omega
  have hrec := (flip49_blank_standard k).pose .north (-56, -30)
  unfold flip49 at hrec
  rw [← flipCell_pose, ← blank_run_entry] at hrec
  have hq : (run blank (12080 + phase49Time k)).pos = q := by simpa using hc.1
  have he : run (singleBlack q) (12080 + phase49Time k) =
      flipCell (run blank (12080 + phase49Time k)) (run blank (12080 + phase49Time k)).pos := by
    rw [singleBlack_eq_perturb, firstContact_state hc, flipCell_eq_perturb, hq]
  rw [← he] at hrec
  exact hrec.of_run

/-- Every single black cell first reached by the blank orbit at time at least 13952. -/
theorem singleBlack_late_all {q : Point} {tau : Nat}
    (hc : FirstContact (fun x => decide (x = q)) blank tau) (hlate : 13952 <= tau) :
    EventuallyStandard (singleBlack q) := by
  by_cases h49 : (tau - 12080) % 104 = 49
  · exact singleBlack_phase49 hc (by omega) h49
  · exact singleBlack_late_explicit hc hlate h49


end LangtonsAnt
