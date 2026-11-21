import PeriodicWordReduction
import PeriodicWordSmall

open LangtonsAnt

#print axioms checkConsistentWord_iff
#print axioms mem_priorPhases
#print axioms period_overlap_bound
#print axioms no_consistent_word_odd
#print axioms board_visit_parity
#print axioms HighwayFrom.exists_white_copy
#print axioms HighwayFrom.visits_phase_perm
#print axioms periodic_tail_consistent_at_start
#print axioms periodic_tail_consistent
#print axioms no_odd_periodic_tail
#print axioms mem_priorPhases_iff_integer_period
#print axioms biPeriodicPos_injective_period
#print axioms checkNoWords_sound
#print axioms checkNoWords_of_blocks
#print axioms checkNoWords_twelve
#print axioms no_consistent_word_small
#print axioms no_periodic_tail_small
#print axioms standard_word_consistent
#print axioms consistentWordsAreStandard_implies_periodicIsStandard
#print axioms highwayConjecture_of_ballistic_and_consistentWordsAreStandard
#print axioms repeatWord_visits_phase_perm
#print axioms wordRealization_support_bound
#print axioms ConsistentWord.realization_run
#print axioms ConsistentWord.realizable
#print axioms consistentWord_iff_finite_realization
#print axioms periodicIsStandard_implies_consistentWordsAreStandard
#print axioms periodicIsStandard_iff_consistentWordsAreStandard
#print axioms highwayConjecture_iff_ballistic_and_consistentWordsAreStandard

example (w : Nat -> Bool) : ¬ ConsistentWord 0 w := by
  intro h
  exact h.2.1 rfl

example (w : Nat -> Bool) : ¬ ConsistentWord 105 w := no_consistent_word_odd (by decide) w

example : checkConsistentWord 4 (fun _ => false) = false := by decide +kernel

example : checkEarlierPhase (fun n => if n = 0 then (0, 0) else (0, -2))
    (0, -1) 0 1 = true := by decide +kernel

example : checkEarlierPhase (fun n => if n = 0 then (0, 0) else (0, -2))
    (0, 1) 0 1 = false := by decide +kernel

example : checkConsistentWord 104 certifiedColor = true :=
  (checkConsistentWord_iff 104 certifiedColor).mpr standard_word_consistent

example (s : State) (hs : FiniteSupport s.board) (T : Nat) (v : Point) :
    ¬ HighwayFrom s T 13 v := no_periodic_tail_small hs (by decide) (by decide)

example (r : Direction) (origin : Point) :
    ConsistentWord 104 (fun i => readColor (pose r origin highwaySeed.toState) i) := by
  have hh := periodic_tail_consistent_at_start
    (finiteSupport_translate (finiteSupport_rotate highwaySeed_finite r) origin)
    (by decide) ((highwaySeed_highway.rotate r).translate origin)
  simpa only [Nat.zero_add, pose] using hh

-- The realization uses only the finite prefix, even if all later supplied bits are wrong.
example (n : Nat) :
    readColor (wordRealization 104
      (fun i => if i < 104 then certifiedColor i else !certifiedColor i)) n = certifiedColor n := by
  have h : ConsistentWord 104
      (fun i => if i < 104 then certifiedColor i else !certifiedColor i) :=
    standard_word_consistent.congr (fun i hi => by simp [hi])
  rw [h.realization_reads (by decide)]
  simp only [Nat.mod_lt _ (by decide : 0 < 104), ite_true, certifiedColor, Nat.mod_mod]

-- A concrete finite seed is supplied without evaluating its 21632 prescribed steps.
example : exists s : State,
    (exists cells : List Point, cells.length = 21632 ∧
      forall p, s.board p = true -> p ∈ cells) ∧
    HighwayFrom s 0 104 (wordDrift 104 certifiedColor) ∧
    forall n, readColor s n = certifiedColor n := by
  refine ⟨wordRealization 104 certifiedColor, wordRealization_support_bound 104 certifiedColor,
    standard_word_consistent.realization_highway (by decide), ?_⟩
  intro n
  rw [standard_word_consistent.realization_reads (by decide)]
  simp only [certifiedColor, Nat.mod_mod]
