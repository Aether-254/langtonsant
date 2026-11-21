import RecoveryCertificate
import DelayedRecovery

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem mature_phase_five_check : checkRecovery 1253 6645 (-37, -35) = true := by
  decide +kernel

theorem mature_phase_five_certificate : RecoveryCertificate 1253 6645 (-37, -35) :=
  checkRecovery_sound mature_phase_five_check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem phase_sixty_six_check : checkRecovery 66 174 (-4, -4) = true := by
  decide +kernel

theorem phase_sixty_six_certificate : RecoveryCertificate 66 174 (-4, -4) :=
  checkRecovery_sound phase_sixty_six_check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem phase_ninety_four_check : checkRecovery 94 238 (-6, -6) = true := by
  decide +kernel

theorem phase_ninety_four_certificate : RecoveryCertificate 94 238 (-6, -6) :=
  checkRecovery_sound phase_ninety_four_check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem phase_ninety_five_check : checkRecovery 95 337 (-6, -6) = true := by
  decide +kernel

theorem phase_ninety_five_certificate : RecoveryCertificate 95 337 (-6, -6) :=
  checkRecovery_sound phase_ninety_five_check

theorem highway_flip_recovers_at_mature_phase_five {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    StandardHighwayFrom (flipCell (run s (104 * k + 1253)) (run s (104 * k + 1253)).pos)
      6645 (-2, -2) := mature_phase_five_certificate.after_blocks h k

theorem phaseFive_position : (highwaySeed.run 5).pos = (-3, -2) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem standard_cycle_phase_five_line_check :
    forall j : Fin 104, let p := (highwaySeed.run j.val).pos
      p.1 + 1 = p.2 -> -5 < p.1 := by
  decide +kernel

theorem phaseFive_first_in_cycle_check :
    forall j : Fin 5, (highwaySeed.run j.val).pos ≠ (-3, -2) := by decide +kernel

theorem phaseFive_first_visit (k : Nat) :
    (run highwaySeed.toState (104 * k + 5)).pos = addPoint (offset (-2, -2) k) (-3, -2) ∧
    forall n, n < 104 * k + 5 ->
      (run highwaySeed.toState n).pos ≠ addPoint (offset (-2, -2) k) (-3, -2) := by
  have hrun (n : Nat) : (highwaySeed.run n).pos = (run highwaySeed.toState n).pos :=
    congrArg State.pos (highwaySeed.toState_run n)
  constructor
  · have hp := (highwaySeed_certificate.block_prefix k 5 (by decide)).pos
    change _ = addPoint (offset (-2, -2) k) (run highwaySeed.toState 5).pos at hp
    rw [← hrun 5, phaseFive_position] at hp
    exact hp
  · intro n hn he
    let q := n / 104
    let j := n % 104
    have hj : j < 104 := Nat.mod_lt _ (by decide)
    have hdecomp : 104 * q + j = n := Nat.div_add_mod n 104
    have hp := (highwaySeed_certificate.block_prefix q j (by omega)).pos
    rw [hdecomp] at hp
    rw [hp] at he
    change addPoint (offset (-2, -2) q) (run highwaySeed.toState j).pos = _ at he
    have hq : q <= k := by omega
    by_cases hsame : q = k
    · have heq : (run highwaySeed.toState j).pos = (-3, -2) := by
        rw [hsame] at he
        apply Prod.ext <;> simp only [addPoint, Prod.mk.injEq] at he ⊢ <;> omega
      have hj5 : j < 5 := by omega
      have hc := phaseFive_first_in_cycle_check ⟨j, hj5⟩
      exact hc ((hrun j).trans heq)
    · have hlt : q < k := by omega
      have hc := standard_cycle_phase_five_line_check ⟨j, hj⟩
      change (highwaySeed.run j).pos.1 + 1 = (highwaySeed.run j).pos.2 ->
        -5 < (highwaySeed.run j).pos.1 at hc
      rw [hrun] at hc
      rw [southwest_offset, southwest_offset] at he
      simp only [addPoint, Prod.mk.injEq] at he
      have hequal : (run highwaySeed.toState j).pos.1 + 1 = (run highwaySeed.toState j).pos.2 := by omega
      have hb := hc hequal
      omega

def phaseFiveObstacle (k : Nat) : Point := (-83 - 2 * (k : Int), -56 - 2 * (k : Int))

def phaseFiveContactTime (k : Nat) : Nat := 13333 + 104 * k

theorem phaseFiveObstacle_first_visit (k : Nat) :
    (run blank (phaseFiveContactTime k)).pos = phaseFiveObstacle k ∧
    forall n, n < phaseFiveContactTime k -> (run blank n).pos ≠ phaseFiveObstacle k := by
  have ht : phaseFiveContactTime k = 12080 + (104 * (k + 12) + 5) := by
    unfold phaseFiveContactTime
    omega
  have hp : phaseFiveObstacle k =
      addPoint (-56, -30) (addPoint (offset (-2, -2) (k + 12)) (-3, -2)) := by
    rw [southwest_offset]
    apply Prod.ext <;> simp [phaseFiveObstacle, addPoint] <;> omega
  have hv := phaseFive_first_visit (k + 12)
  constructor
  · rw [ht, blank_tail_pos, hv.1, hp]
  · intro n hn he
    by_cases hearly : n < 12080
    · have hb := checkPackedEntry_inBox blank_entry_check n hearly
      rw [packedBlank_toState, he] at hb
      simp only [InBox, phaseFiveObstacle] at hb
      omega
    · have hn' : n = 12080 + (n - 12080) := by omega
      rw [hn', blank_tail_pos, hp] at he
      have hpos : (run highwaySeed.toState (n - 12080)).pos =
          addPoint (offset (-2, -2) (k + 12)) (-3, -2) := by
        apply Prod.ext <;> simp only [addPoint, Prod.mk.injEq] at he ⊢ <;> omega
      exact hv.2 (n - 12080) (by omega) hpos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem phaseFiveObstacle_standard (k : Nat) :
    StandardHighwayFrom (singleBlack (phaseFiveObstacle k)) (19978 + 104 * k) (-2, -2) := by
  have hsum : phaseFiveContactTime k + 6645 = 19978 + 104 * k := by
    unfold phaseFiveContactTime
    omega
  have ht : 12080 + (104 * k + 1253) = phaseFiveContactTime k := by
    unfold phaseFiveContactTime
    omega
  have hv := phaseFiveObstacle_first_visit k
  have hf : FirstContact (fun q => decide (q = phaseFiveObstacle k)) blank (phaseFiveContactTime k) := by
    refine ⟨by simp [hv.1], ?_⟩
    intro j hj
    simp [hv.2 j hj]
  have he : run (singleBlack (phaseFiveObstacle k)) (phaseFiveContactTime k) =
      flipCell (run blank (phaseFiveContactTime k)) (run blank (phaseFiveContactTime k)).pos := by
    rw [singleBlack_eq_perturb, firstContact_state hf, flipCell_eq_perturb, hv.1]
  have hr := mature_phase_five_certificate.after_entry blank_entryAt k
  rw [ht, ← he] at hr
  have hh := hr.of_run
  simpa only [hsum, rotatePoint] using hh

end LangtonsAnt
