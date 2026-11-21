import HardPhaseRecovery

open LangtonsAnt

/-! Sanity checks for `FreshPhases.lean`.  Not a proof dependency. -/

-- The classification agrees with the independently proved phase-4 first visit.
example (k : Nat) (hk : 2 <= k) : FirstVisitAt highwaySeed.toState (104 * k + 4) :=
  (seed_firstVisit_iff hk (by decide)).mpr (by decide)

example (k : Nat) : FirstVisitAt highwaySeed.toState (104 * k + 4) := by
  intro j hj
  rw [(phaseFour_first_visit k).1]
  exact (phaseFour_first_visit k).2 j hj

-- All previously certified recovery phases are first-visit phases.
example : [4, 5, 66, 94, 95].all (· ∈ freshPhases) = true := by decide

-- Phases still lacking a recovery certificate.
example : freshPhases.filter (· ∉ [4, 5, 66, 94, 95]) =
    [6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 96] := by decide

-- A non-fresh phase: phase 0 of any period k >= 2 is a revisit.
example (k : Nat) (hk : 2 <= k) : ¬FirstVisitAt highwaySeed.toState (104 * k + 0) := by
  rw [seed_firstVisit_iff hk (by decide)]
  decide

-- Symbolic period: the statement is for all k >= 2, not a finite range.
example : forall k, 2 <= k ->
    (FirstVisitAt highwaySeed.toState (104 * k + 96) ↔ True) := by
  intro k hk
  rw [seed_firstVisit_iff hk (by decide)]
  decide

-- Recovery: 21 of the 22 first-visit phases, for every history and every later period.
example (s : State) (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    exists H, EventuallyStandard
      (flipCell (run s (104 * (k + H) + 96)) (run s (104 * (k + H) + 96)).pos) := by
  obtain ⟨H, hH⟩ := fresh_phase_recovers_except_49 96 (by decide) (by decide)
  exact ⟨H, hH s h k⟩

#print axioms fresh_phase_recovers_except_49
#print axioms certified_fresh_phase_recovers
#print axioms RotatedRecoveryCertificate.after_blocks
#print axioms checkShiftedRecovery_sound
#print axioms seed_fresh_phase_classification
#print axioms seed_firstVisit_iff
#print axioms seed_late_cell_white
