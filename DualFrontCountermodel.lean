import PeriodicBackgroundWord
import RecordPair

namespace LangtonsAnt

/-- The finite test for a record in the bi-infinite extension of a level trace. -/
def cyclicRecordCheck (P : Nat) (level : Nat -> Int) (drift : Int) (i : Nat) : Bool :=
  (List.range P).all (fun j => decide (level j - (if j < i then 0 else drift) < level i))

/-- Previous periods are indexed by `k`; in period zero only phases before `i` count. -/
def PastPeriodRecord (P : Nat) (level : Nat -> Int) (drift : Int) (i : Nat) : Prop :=
  forall k j : Nat, j < P -> (0 < k ∨ j < i) -> level j - (k : Int) * drift < level i

theorem cyclicRecordCheck_iff {P i : Nat} {level : Nat -> Int} {drift : Int}
    (hd : 0 < drift) :
    cyclicRecordCheck P level drift i = true ↔ PastPeriodRecord P level drift i := by
  simp only [cyclicRecordCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h k j hj hk
    have hh := h j hj
    by_cases hz : k = 0
    · subst k
      have hji : j < i := by omega
      simpa [hji] using hh
    · have hmul : drift <= (k : Int) * drift := by
        have hh := Int.mul_le_mul_of_nonneg_right (show (1 : Int) <= k by omega) (Int.le_of_lt hd)
        simpa using hh
      split at hh <;> omega
  · intro h j hj
    by_cases hji : j < i
    · have hh := h 0 j hj (Or.inr hji)
      simpa [hji] using hh
    · have hh := h 1 j hj (Or.inl (by decide))
      simpa [hji] using hh

namespace DualFrontCountermodel

/-- Found by the deliberately relaxed search in scripts/dual_front_probe.py. -/
def word (n : Nat) : Bool :=
  decide (n % 44 ∈ [0, 5, 8, 13, 15, 16, 18, 19, 22, 23, 25, 27, 32, 35, 40, 42])

-- Coordinates are rotated from the search's east-facing origin to a north-facing origin.
def background (p : Point) : Bool :=
  decide ((p.1, p.2 % 4) ∈ [(0, 0), (-2, 0), (-4, 3), (-4, 2), (1, 3), (2, 3), (2, 1)])

theorem drift : wordDrift 44 word = (0, 4) := by decide +kernel

theorem background_word : BackgroundWord 44 word background := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · rw [drift]; decide
  · intro p
    rw [drift]
    simp [background, addPoint]
  · have h : forall i : Fin 44, word i = Bool.xor (background (wordPos word i))
        (decide ((priorPhases 44 word i).length % 2 = 1)) := by decide +kernel
    exact fun i hi => h ⟨i, hi⟩

def seed : State := backgroundRealization 44 word background

theorem highway : HighwayFrom seed 0 44 (0, 4) := by
  simpa only [seed, drift] using background_word.realization_highway (by decide)

theorem reads (n : Nat) : readColor seed n = word (n % 44) :=
  background_word.realization_reads (by decide) n

theorem not_consistent : ¬ ConsistentWord 44 word := by
  have hc : checkConsistentWord 44 word = false := by decide +kernel
  intro h
  rw [(checkConsistentWord_iff 44 word).mpr h] at hc
  contradiction

theorem not_finite : ¬ FiniteSupport seed.board := by
  intro hf
  apply not_consistent
  have hc := periodic_tail_consistent_at_start hf (by decide : 0 < 44) highway
  apply hc.congr
  intro j hj
  simp only [Nat.zero_add, reads, Nat.mod_eq_of_lt hj]

def level (sx : Int) (n : Nat) : Int := linearForm sx 1 (wordPos word n)

def records (sx : Int) : List Nat :=
  (List.range 44).filter (cyclicRecordCheck 44 (level sx) 4)

def pairStarts (sx : Int) : List Nat :=
  (records sx).filter (fun i => decide (gain sx 1 (wordTrace word i).2.right = 1))

theorem records_left : records (-1) = [1, 2, 9, 10] := by decide +kernel

theorem records_right : records 1 = [28, 29, 36, 37] := by decide +kernel

theorem pair_starts_left : pairStarts (-1) = [1, 9] := by decide +kernel

theorem pair_starts_right : pairStarts 1 = [28, 36] := by decide +kernel

theorem records_are_genuine (sx : Int) (i : Nat) (hi : i ∈ records sx) :
    PastPeriodRecord 44 (level sx) 4 i :=
  (cyclicRecordCheck_iff (by decide)).mp (List.mem_filter.mp hi).2

def hasFrontFactor (i : Nat) : Bool :=
  word ((i + 43) % 44) && !word i && !word ((i + 1) % 44) &&
    !word ((i + 2) % 44) && !word ((i + 3) % 44) && word ((i + 4) % 44)

theorem all_records_white : ((records (-1) ++ records 1).all (fun i => !word i)) = true := by
  decide +kernel

theorem both_front_factors :
    ((pairStarts (-1) ++ pairStarts 1).all hasFrontFactor) = true := by
  decide +kernel

theorem both_drifts_positive : linearForm (-1) 1 (wordDrift 44 word) = 4 ∧
    linearForm 1 1 (wordDrift 44 word) = 4 := by rw [drift]; decide

/-- All four leading L events have no earlier physical visit in the bi-infinite path.
Their black colour is supplied by the background, not by a previous white read. -/
theorem unsupported_black_inputs : forall i : Fin 44, i.val ∈ [0, 8, 27, 35] ->
    word i = true ∧ priorPhases 44 word i = [] := by
  decide +kernel

theorem nonstandard_read_period : word 2 ≠ word ((2 + 104) % 44) := by decide +kernel

theorem no_standard_tail (T : Nat) (v : Point) : ¬ HighwayFrom seed T 104 v := by
  intro h
  have hh := h.reads_periodic (n := 44 * T + 2) (by omega)
  rw [reads, reads] at hh
  rw [show (44 * T + 2 + 104) % 44 = (2 + 104) % 44 by omega,
    show (44 * T + 2) % 44 = 2 by omega] at hh
  exact nonstandard_read_period hh.symm

theorem not_eventually_standard : ¬ EventuallyStandard seed := by
  rintro ⟨T, v, _, hh⟩
  exact no_standard_tail T v hh.1

end DualFrontCountermodel

end LangtonsAnt
