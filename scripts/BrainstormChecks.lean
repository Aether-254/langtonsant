import AxisClockObstruction
import RecordSupport
import RecordSupportExamples
import DualFrontCountermodel

open LangtonsAnt

#print axioms AxisClockObstruction.east_four
#print axioms AxisClockObstruction.west_four
#print axioms AxisClockObstruction.increment_cancellation
#print axioms AxisClockObstruction.no_universal_strict_clock
#print axioms black_has_white_source
#print axioms finiteSupport_white_above
#print axioms record_support_pose
#print axioms record_black_has_support_excursion
#print axioms record_predecessor_max
#print axioms record_base_heading
#print axioms record_base_prior_white
#print axioms white_reads_final_white_no_visit
#print axioms record_black_has_first_return
#print axioms same_front_sources_ordered
#print axioms RecordSupportExamples.prefix_checked
#print axioms RecordSupportExamples.blank_records
#print axioms RecordSupportExamples.blank_sources
#print axioms RecordSupportExamples.crossing_distinct_fronts
#print axioms RecordSupportExamples.blank_front_pause
#print axioms RecordSupportExamples.source_link_fails
#print axioms RecordSupportExamples.standard_sources
#print axioms BackgroundWord.realization_run
#print axioms BackgroundWord.realization_highway
#print axioms cyclicRecordCheck_iff
#print axioms DualFrontCountermodel.background_word
#print axioms DualFrontCountermodel.highway
#print axioms DualFrontCountermodel.reads
#print axioms DualFrontCountermodel.not_finite
#print axioms DualFrontCountermodel.records_are_genuine
#print axioms DualFrontCountermodel.both_front_factors
#print axioms DualFrontCountermodel.unsupported_black_inputs
#print axioms DualFrontCountermodel.no_standard_tail
#print axioms DualFrontCountermodel.not_eventually_standard

example : ¬ ConsistentWord 44 DualFrontCountermodel.word :=
  DualFrontCountermodel.not_consistent

example : PastPeriodRecord 44 (DualFrontCountermodel.level (-1)) 4 1 :=
  DualFrontCountermodel.records_are_genuine _ _ (by
    rw [DualFrontCountermodel.records_left]; decide)

-- A constant level cannot create a record; this protects the positive-drift interpretation.
example : cyclicRecordCheck 4 (fun _ => 0) 0 1 = false := by decide +kernel

example : AxisClockObstruction.TwoPeriodic (fun p => p.2 * p.2) := by
  intro x y; rfl
