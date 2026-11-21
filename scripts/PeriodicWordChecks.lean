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
