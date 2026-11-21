# Independent review brief for Claude

## Objective

Review the mathematical route toward the classical RL Langton ant highway conjecture in this Lean repository. The conjecture for every finite black initial configuration remains unproved here. Prioritize an independent examination of the remaining general argument over more examples of special obstacle chains.

The model is the infinite integer square grid. White turns right, black turns left; the ant then flips the current cell and moves. Initial position and heading are arbitrary in the conjecture. Main proof files are at the repository root; research belongs in `research/` or `drafts/`. Lean 4.36.0 uses only bundled `Std`, with no Mathlib.

## Read first

1. `drafts/proof-status.md`: proved results, their limits, and build instructions.
2. `LangtonsAnt.lean`: `FiniteSupport`, `HighwayFrom`, `StandardHighwayFrom`, and `HighwayConjecture`.
3. `SingleFlipReduction.lean`: `CurrentCellFlipStability`, `ArbitraryCellFlipStability`, and `highwayConjecture_iff_currentCellFlipStability`.
4. `HighwayEntrance.lean`, `EntranceChecker.lean`, and `TrajectoryCoupling.lean`: eventual standard behavior, certificate entry, and detector equivalences.
5. `HighwayRecovery.lean`, `RecoveryCertificate.lean`, and `MaturePhaseRecovery.lean`: the precise hypotheses under which local flips have already been proved to recover.

## Main question

The formalized remaining proposition is:

```lean
def CurrentCellFlipStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    EventuallyStandard (flipCell s s.pos)
```

Its equivalence to `HighwayConjecture` is already proved. The hard case includes states whose certified highway begins only later, and arbitrary finite histories outside currently certified regions. A proof for flipping a particular mature highway phase does not establish this proposition.

Please examine the following issues:

- Are the definitions and quantifiers faithful to the intended mathematical conjecture? Kernel acceptance establishes the stated propositions, but does not establish that the chosen statement captures the intended target.
- Can one identify a genuinely useful invariant, induction measure, or stronger intermediate hypothesis that makes the single-flip step tractable? State it precisely, and separate proved implications from the new unproved ingredient.
- Which tempting generalizations of the local recovery certificates fail? Give a rigorous counterexample to a candidate lemma when possible, or a reproducible experiment clearly labeled as incomplete evidence.
- Can finite support force eventual entry into one of the certified half-plane states by an argument stronger than unboundedness of the visited set? Avoid replacing this question with a restatement of the original conjecture.

## Established stress tests

- Infinite equally spaced obstacle chains can have minimal period `548+104*k` and drift `(-8-2*k,-8-2*k)`.
- Infinite chains with arbitrarily late, arbitrarily large gap parameters have no eventual positive read period or translational highway.
- Every finite truncation of those constructed chains eventually becomes standard and agrees with the infinite chain on each sufficiently short observation window.
- For a retained chain `p_0,...,p_n`, write `T_0=0` and `T_(i+1)=T_i+548+104*f(i)`. The exact first visit of `p_i` is `12604+T_i`; the exact earliest permanent geometric 104-step highway starts at `12915+T_n`. A standard-reference phase-aligned certificate starts at `12940+T_n`.

These results are in `VariableFirstVisits.lean`, `VariableRecoveryBounds.lean`, and `ExactVariableRecovery.lean`, with earlier infinite-chain proofs in `SpacedHighwayClassification.lean` and `AperiodicObstacleChain.lean`. Infinite-support examples are not counterexamples to the finite-support conjecture. Pointwise agreement on finite observation windows does not imply convergence of eventual-periodicity properties.

## Deliverable and coordination

Write the review in Chinese in `research/claude-review.md`. For each claim, provide a precise statement, necessary assumptions, supporting file/theorem names, and either a proof, counterexample, or explicitly identified missing step. Lean statements or small independent proof attempts are welcome. Keep exploratory artifacts under `research/` or `drafts/` and avoid editing existing root Lean files while the other agent is working.

Do not treat a finite simulation as proof of an infinite-time claim. Do not assume the highway conjecture or single-flip stability while claiming to prove it. A precise obstruction or a failed candidate lemma with a concrete witness is useful progress; an unsupported full proof is not.
