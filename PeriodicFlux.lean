import DualFrontCountermodel
import PeriodicGrowthResidue

/-!
# Positive growth, seven black input phases, and non-white-consistency of the 44-word

This module records the finite flux test on the existing 44-letter word
`DualFrontCountermodel.word`, which is already known in this repository to carry a
`BackgroundWord` implementation on a periodic background and to have full drift `(0, 4)`. It
proves that this word has integral drift-compatible growth `12` (`mixed44_positive_growth_C`),
that its black input phases — the phases whose read color is black while no earlier phase of
the same translation class has an empty `priorPhases` set — are exactly
`[0, 8, 15, 16, 27, 35, 42]`, giving `A = 7` (`mixed44_black_input_phases_C`), and that the
word is simultaneously background-realizable and positively growing yet fails
`ConsistentWord 44` (`mixed44_positive_growth_not_white_C`). Consequently a positive-growth
segment with a genuine background realization need not be a white-background consistent
word, so forbidding net-negative-growth segments alone cannot carry the C-D to C-M reduction.

Provenance: research/persist-C-periodic-tail-2026-11-23.md, session 2, written by
GPT-6 Astra. The session-2 material is integrated unchanged apart from wrapping the
declarations in the namespace `LangtonsAnt.PeriodicFlux` and deleting the scratch file's
trailing diagnostic lines; every definition and proof is verbatim.
-/

namespace LangtonsAnt.PeriodicFlux

def blackInputPhasesC (P : Nat) (w : Nat -> Bool) : List Nat :=
  (List.range P).filter (fun i => w i && (priorPhases P w i).isEmpty)

theorem mixed44_positive_growth_C : wordGrowthInt 44 DualFrontCountermodel.word = 12 := by
  decide +kernel

theorem mixed44_black_input_phases_C :
    blackInputPhasesC 44 DualFrontCountermodel.word = [0, 8, 15, 16, 27, 35, 42] := by
  decide +kernel

theorem mixed44_positive_growth_not_white_C :
    (exists background, BackgroundWord 44 DualFrontCountermodel.word background) ∧
    0 < wordGrowthInt 44 DualFrontCountermodel.word ∧
    ¬ConsistentWord 44 DualFrontCountermodel.word := by
  refine ⟨⟨DualFrontCountermodel.background, DualFrontCountermodel.background_word⟩, ?_,
    DualFrontCountermodel.not_consistent⟩
  rw [mixed44_positive_growth_C]
  decide

end LangtonsAnt.PeriodicFlux
