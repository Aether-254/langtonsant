import Phase49K2_13

/-! Final segment and assembly of the phase-49 prefix check (generated). -/

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem k2Final : checkTrailPrefix g49 (-26) trailPackedTarget 421 k2State13 = true := by
  decide +kernel

theorem trail_prefix_guard (j : Nat) (hj : j < trailDelay) :
    g49 (run trailPackedInput.toPacked.toState j).pos = true := by
  have s1 := checkTrailSeg_sound k2Seg1
  have s2 := checkTrailSeg_sound k2Seg2
  have s3 := checkTrailSeg_sound k2Seg3
  have s4 := checkTrailSeg_sound k2Seg4
  have s5 := checkTrailSeg_sound k2Seg5
  have s6 := checkTrailSeg_sound k2Seg6
  have s7 := checkTrailSeg_sound k2Seg7
  have s8 := checkTrailSeg_sound k2Seg8
  have s9 := checkTrailSeg_sound k2Seg9
  have s10 := checkTrailSeg_sound k2Seg10
  have s11 := checkTrailSeg_sound k2Seg11
  have s12 := checkTrailSeg_sound k2Seg12
  have s13 := checkTrailSeg_sound k2Seg13
  have sF := checkTrailPrefix_sound k2Final
  have r1 : run trailPackedInput.toPacked.toState 4000 = k2State1.toState := s1.2
  have r2 : run trailPackedInput.toPacked.toState 8000 = k2State2.toState := by
    rw [show (8000 : Nat) = 4000 + 4000 from rfl, run_add, r1]
    exact s2.2
  have r3 : run trailPackedInput.toPacked.toState 12000 = k2State3.toState := by
    rw [show (12000 : Nat) = 8000 + 4000 from rfl, run_add, r2]
    exact s3.2
  have r4 : run trailPackedInput.toPacked.toState 16000 = k2State4.toState := by
    rw [show (16000 : Nat) = 12000 + 4000 from rfl, run_add, r3]
    exact s4.2
  have r5 : run trailPackedInput.toPacked.toState 20000 = k2State5.toState := by
    rw [show (20000 : Nat) = 16000 + 4000 from rfl, run_add, r4]
    exact s5.2
  have r6 : run trailPackedInput.toPacked.toState 24000 = k2State6.toState := by
    rw [show (24000 : Nat) = 20000 + 4000 from rfl, run_add, r5]
    exact s6.2
  have r7 : run trailPackedInput.toPacked.toState 28000 = k2State7.toState := by
    rw [show (28000 : Nat) = 24000 + 4000 from rfl, run_add, r6]
    exact s7.2
  have r8 : run trailPackedInput.toPacked.toState 32000 = k2State8.toState := by
    rw [show (32000 : Nat) = 28000 + 4000 from rfl, run_add, r7]
    exact s8.2
  have r9 : run trailPackedInput.toPacked.toState 36000 = k2State9.toState := by
    rw [show (36000 : Nat) = 32000 + 4000 from rfl, run_add, r8]
    exact s9.2
  have r10 : run trailPackedInput.toPacked.toState 40000 = k2State10.toState := by
    rw [show (40000 : Nat) = 36000 + 4000 from rfl, run_add, r9]
    exact s10.2
  have r11 : run trailPackedInput.toPacked.toState 44000 = k2State11.toState := by
    rw [show (44000 : Nat) = 40000 + 4000 from rfl, run_add, r10]
    exact s11.2
  have r12 : run trailPackedInput.toPacked.toState 48000 = k2State12.toState := by
    rw [show (48000 : Nat) = 44000 + 4000 from rfl, run_add, r11]
    exact s12.2
  have r13 : run trailPackedInput.toPacked.toState 52000 = k2State13.toState := by
    rw [show (52000 : Nat) = 48000 + 4000 from rfl, run_add, r12]
    exact s13.2
  unfold trailDelay at hj
  by_cases c1 : j < 4000
  · exact s1.1 j c1
  by_cases c2 : j < 8000
  · have hg := guard_shift r1 s2.1 (j - 4000) (by omega)
    rwa [show 4000 + (j - 4000) = j by omega] at hg
  by_cases c3 : j < 12000
  · have hg := guard_shift r2 s3.1 (j - 8000) (by omega)
    rwa [show 8000 + (j - 8000) = j by omega] at hg
  by_cases c4 : j < 16000
  · have hg := guard_shift r3 s4.1 (j - 12000) (by omega)
    rwa [show 12000 + (j - 12000) = j by omega] at hg
  by_cases c5 : j < 20000
  · have hg := guard_shift r4 s5.1 (j - 16000) (by omega)
    rwa [show 16000 + (j - 16000) = j by omega] at hg
  by_cases c6 : j < 24000
  · have hg := guard_shift r5 s6.1 (j - 20000) (by omega)
    rwa [show 20000 + (j - 20000) = j by omega] at hg
  by_cases c7 : j < 28000
  · have hg := guard_shift r6 s7.1 (j - 24000) (by omega)
    rwa [show 24000 + (j - 24000) = j by omega] at hg
  by_cases c8 : j < 32000
  · have hg := guard_shift r7 s8.1 (j - 28000) (by omega)
    rwa [show 28000 + (j - 28000) = j by omega] at hg
  by_cases c9 : j < 36000
  · have hg := guard_shift r8 s9.1 (j - 32000) (by omega)
    rwa [show 32000 + (j - 32000) = j by omega] at hg
  by_cases c10 : j < 40000
  · have hg := guard_shift r9 s10.1 (j - 36000) (by omega)
    rwa [show 36000 + (j - 36000) = j by omega] at hg
  by_cases c11 : j < 44000
  · have hg := guard_shift r10 s11.1 (j - 40000) (by omega)
    rwa [show 40000 + (j - 40000) = j by omega] at hg
  by_cases c12 : j < 48000
  · have hg := guard_shift r11 s12.1 (j - 44000) (by omega)
    rwa [show 44000 + (j - 44000) = j by omega] at hg
  by_cases c13 : j < 52000
  · have hg := guard_shift r12 s13.1 (j - 48000) (by omega)
    rwa [show 48000 + (j - 48000) = j by omega] at hg
  have hg := guard_shift r13 sF.1 (j - 52000) (by omega)
  rwa [show 52000 + (j - 52000) = j by omega] at hg

theorem trail_prefix_avoid2 (j : Nat) (hj : j < trailDelay) :
    avoidJunk2 (run trailStart j).pos = true := by
  have h := trail_prefix_guard j hj
  rw [trailPackedInput_toState, trailFrame_run] at h
  unfold g49 at h
  rw [trailUnframe_pos] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end LangtonsAnt
