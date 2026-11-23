# Langton's Ant: Lean 4 formalization and research notes

This repository contains Lean 4 (v4.36.0, no Mathlib) proofs and research notes about
Langton's ant, in particular the structure of periodic highways reached from finite initial states.

- `drafts/proof-status.md` (in Chinese) lists every result, its trust base and its source.
- The default libraries `LangtonsAnt` and `PeriodicWords` are pure kernel proofs whose axioms are
  only `propext`, `Classical.choice` and `Quot.sound`. `scripts/Checks20261123.lean` audits the
  modules added on 2026-11-23.
- `PeriodicNative` modules use `native_decide` and therefore also trust the Lean compiler; they are
  kept separate and labelled.
- `SingleBlackEarly` and `SingleBlackFull` are large kernel certificates. Do not build them with
  plain `lake build`; see the comments in `lakefile.toml`.
- `research/` holds dated working notes. Statements there are paper proofs or experiments unless a
  Lean module is cited.

The general highway conjecture for finite initial states remains open; nothing here claims it.

Copyright (c) 2026 Aether-254. All rights reserved.
