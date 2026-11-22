import TwoCellDiagonalRank

/-!
# Two-cell diagonal exclusion (`g ≠ 4`), Ke Theorem C, and rotation reduction (L24–L25, L28)

This module closes the two-cell diagonal branch of `research/growth-blueprint-2026-11-22.md`
purely in the Lean kernel (zero `sorry`, zero `axiom`, zero `native_decide`):

- **L24 (`TwoCellDiagonal.not_pureOddWake`, `TwoCellDiagonal.drift_two_negTwo_growth_ne_four`,
  `TwoCellDiagonal.drift_two_negTwo_checker_mixed`):** Refutes `PureOddWake` for drift `(2, -2)`
  by combining `pureOdd_leftRankSum_parity`, `pureOdd_edgeCross_eq_chain`,
  `pureOdd_twoLane_chain_parity_zero`, and `leftRankSum_mod_two_eq_zero`, proving `wordGrowth ≠ 4`
  and Ke Theorem C (`2 ≤ n_+ ∧ 2 ≤ n_-`, both even) at drift `(2, -2)`.
- **L25 & L28 (`ConsistentWord.twoCellDiagonal_growth_ne_four`,
  `ConsistentWord.twoCellDiagonal_checker_mixed`, `periodic_tail_twoCellDiagonal_growth_ne_four`,
  `periodic_tail_twoCellDiagonal_checker_mixed`):** Quarter-turn/shift reduction to every
  `TwoCellDiagonalDrift`, with explicit `checkerSign` flip bookkeeping on odd shifts (`checker_counts_shift`).
- **Sanity (`stdHighwaySE_theorem_C_sanity`):** Verifies both `stdHighwaySE` (`g = 12`, drift `(2, -2)`)
  and `certifiedColor` (`g = 12`, drift `(-2, -2)`) satisfy the headline theorems.
-/

namespace LangtonsAnt
namespace TwoCellDiagonal

/-! ## 1. L24: Refuting `PureOddWake`, `g ≠ 4`, and Ke Theorem C at drift `(2, -2)` -/

/-- **L24 (core refutation):** No consistent word with full drift `(2, -2)` can have all odd
translation classes on odd layers (`PureOddWake`). -/
theorem not_pureOddWake {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    ¬ PureOddWake P w := by
  intro hpure
  have hK0 := leftRankSum_mod_two_eq_zero h hd
  have hK1 := pureOdd_leftRankSum_parity h hd hpure
  have hE := pureOdd_edgeCross_eq_chain h hd hpure
  have hchain := pureOdd_twoLane_chain_parity_zero h hd hpure
  omega

/-- **L24 (`g ≠ 4` at drift `(2, -2)`):** No consistent word with drift `(2, -2)` has growth `4`. -/
theorem drift_two_negTwo_growth_ne_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    wordGrowth P w ≠ 4 := by
  intro hg
  exact not_pureOddWake h hd (drift_two_negTwo_growth_four_all_neg h hd hg).1

private theorem checkerSign_sum_eq_sub_counts (P : Nat) (w : Nat → Bool) :
    ((oddClassReps P w).map (fun i => checkerSign (wordPos w i))).sum =
      (((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length : Int) -
      (((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length : Int) := by
  have haux : ∀ xs : List Nat,
      (xs.map (fun i => checkerSign (wordPos w i))).sum =
        ((xs.filter (fun i => decide (checkerSign (wordPos w i) = 1))).length : Int) -
        ((xs.filter (fun i => decide (checkerSign (wordPos w i) = -1))).length : Int) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rcases checkerSign_eq_one_or_neg_one (wordPos w x) with hx | hx <;>
        simp [hx, ih] <;> omega
  exact haux (oddClassReps P w)

private theorem checkerSign_counts_sum_eq_growth (P : Nat) (w : Nat → Bool) :
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length +
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length =
      wordGrowth P w := by
  have haux : ∀ xs : List Nat,
      (xs.filter (fun i => decide (checkerSign (wordPos w i) = 1))).length +
      (xs.filter (fun i => decide (checkerSign (wordPos w i) = -1))).length = xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rcases checkerSign_eq_one_or_neg_one (wordPos w x) with hx | hx <;>
        simp [hx] <;> omega
  exact haux (oddClassReps P w)

/-- For every `TwoCellDiagonalDrift`, the counts of `χ = +1` and `χ = -1` odd classes are both even. -/
theorem twoCellDiagonal_checker_counts_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellDiagonalDrift (wordDrift P w)) :
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length % 2 = 0 ∧
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length % 2 = 0 := by
  have ha_ne : (wordDrift P w).1 ≠ 0 := by rcases hd.1 with h1 | h1 <;> omega
  have ha_abs : (wordDrift P w).1.natAbs = 2 := by rcases hd.1 with h1 | h1 <;> omega
  have hr0 := h.residue_sum_x_mod_four ha_ne (r := 0) (by omega)
  have hr1 := h.residue_sum_x_mod_four ha_ne (r := 1) (by omega)
  rw [ha_abs] at hr0 hr1
  have hsplit :
      ((oddClassReps P w).map (fun i => checkerSign (wordPos w i))).sum =
      (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 0))).map
        (fun i => checkerSign (wordPos w i))).sum +
      (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 1))).map
        (fun i => checkerSign (wordPos w i))).sum := by
    have haux : ∀ xs : List Nat,
        (xs.map (fun i => checkerSign (wordPos w i))).sum =
        ((xs.filter (fun i => decide ((wordPos w i).1 % 2 = 0))).map
          (fun i => checkerSign (wordPos w i))).sum +
        ((xs.filter (fun i => decide ((wordPos w i).1 % 2 = 1))).map
          (fun i => checkerSign (wordPos w i))).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih =>
        by_cases hx : (wordPos w x).1 % 2 = 0
        · simp [hx, ih]; omega
        · have h1 : (wordPos w x).1 % 2 = 1 := by omega
          simp [h1, ih]; omega
    exact haux (oddClassReps P w)
  have hsub := checkerSign_sum_eq_sub_counts P w
  have htot := checkerSign_counts_sum_eq_growth P w
  have hmod := h.growth_mod_four
  change (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 0))).map
    (fun i => checkerSign (wordPos w i))).sum % 4 = 2 at hr0
  change (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 1))).map
    (fun i => checkerSign (wordPos w i))).sum % 4 = 2 at hr1
  omega

private theorem exists_mem_of_not_forall_dec {α : Type} (p : α → Bool) :
    ∀ xs : List α, ¬ (∀ x ∈ xs, p x = true) → ∃ x ∈ xs, p x = false
  | [], h => False.elim (h (fun _ hx => by simp at hx))
  | x :: xs, h => by
    cases hpx : p x
    · exact ⟨x, by simp, hpx⟩
    · have hrest : ¬ (∀ y ∈ xs, p y = true) := by
        intro hall; apply h; intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hpx
        · exact hall y hy'
      obtain ⟨y, hy, hpy⟩ := exists_mem_of_not_forall_dec p xs hrest
      exact ⟨y, by simp [hy], hpy⟩

/-- **L24 / L28 (Ke Theorem C at drift `(2, -2)`):** Both checkerboard signs occur among odd
translation classes, with an even count `≥ 2` of each sign. -/
theorem drift_two_negTwo_checker_mixed {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    2 ≤ ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length ∧
    2 ≤ ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length := by
  have hneg2 := two_le_neg_oddClassReps h hd
  have hnot_pure := not_pureOddWake h hd
  have hnot_dec : ¬ (∀ i ∈ oddClassReps P w, decide (checkerSign (wordPos w i) = -1) = true) := by
    intro hall
    exact hnot_pure (fun i hi => of_decide_eq_true (hall i hi))
  obtain ⟨i, hiO, hif⟩ := exists_mem_of_not_forall_dec _ (oddClassReps P w) hnot_dec
  have hi1 : checkerSign (wordPos w i) = 1 := by
    rcases checkerSign_eq_one_or_neg_one (wordPos w i) with h1 | hm1
    · exact h1
    · simp [hm1] at hif
  have hpos1 : 1 ≤ ((oddClassReps P w).filter (fun j => decide (checkerSign (wordPos w j) = 1))).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hiO, decide_eq_true hi1⟩)
  have hev := twoCellDiagonal_checker_counts_even h
    ⟨Or.inl (by simp [hd]), Or.inr (by simp [hd])⟩
  omega

/-! ## 2. L25 & L28: Rotation/shift reduction with explicit `checkerSign` flip bookkeeping -/

/-- Every two-cell diagonal drift vector is a quarter turn of `(2, -2)`. -/
theorem exists_rotate_of_twoCellDiagonal {v : Point} (hv : TwoCellDiagonalDrift v) :
    ∃ r : Direction, rotatePoint r (2, -2) = v := by
  obtain ⟨h1, h2⟩ := hv
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ⟨.west, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩
  · exact ⟨.north, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩
  · exact ⟨.south, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩
  · exact ⟨.east, by apply Prod.ext <;> simp [rotatePoint, h1, h2]⟩

theorem twoCellDiagonalDrift_rotatePoint (r : Direction) (v : Point) :
    TwoCellDiagonalDrift (rotatePoint r v) ↔ TwoCellDiagonalDrift v := by
  rcases v with ⟨a, b⟩
  cases r <;> unfold TwoCellDiagonalDrift rotatePoint <;> dsimp only <;> omega

/-- For every turn word `u`, `checkerSign (wordPos u i) = (-1)^i` (independent of `u`). -/
theorem checkerSign_wordPos_eq_parity (u : Nat → Bool) (i : Nat) :
    checkerSign (wordPos u i) = if i % 2 = 0 then 1 else -1 := by
  have hp := wordPos_sum_parity u i
  unfold checkerSign
  by_cases hi : i % 2 = 0
  · have he : ((wordPos u i).1 + (wordPos u i).2) % 2 = 0 := by omega
    simp [hi, he]
  · have ho : ((wordPos u i).1 + (wordPos u i).2) % 2 ≠ 0 := by omega
    simp [hi, ho]

private theorem int_sum_append' (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.cons_append, List.sum_cons, ih]; omega

private theorem altSign_sum_shift_periodic {P : Nat} {u : Nat → Bool}
    (hPeven : P % 2 = 0) (hper : ∀ i, u (i + P) = u i) (a : Nat) :
    ((List.range P).map (fun i => (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + i)))).sum =
      (if a % 2 = 0 then (1 : Int) else -1) *
        ((List.range P).map (fun i => (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u i))).sum := by
  induction a with
  | zero => simp
  | succ a ih =>
    rcases Nat.eq_zero_or_pos P with rfl | hP
    · simp
    · obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
      have hstep :
          ((List.range (Q + 1)).map (fun i =>
            (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + 1 + i)))).sum =
          -((List.range (Q + 1)).map (fun i =>
            (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + i)))).sum := by
        have hL :
            ((List.range (Q + 1)).map (fun i =>
              (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + 1 + i)))).sum =
            ((List.range Q).map (fun i =>
              (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (i + 1))))).sum +
              (if Q % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (Q + 1))) := by
          rw [List.range_succ, List.map_append, int_sum_append']
          simp only [List.map_singleton, List.sum_singleton]
          rw [show a + 1 + Q = a + (Q + 1) by omega]
          congr 1; congr 1
          apply List.map_congr_left
          intro i _
          rw [show a + 1 + i = a + (i + 1) by omega]
        have hR :
            ((List.range (Q + 1)).map (fun i =>
              (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + i)))).sum =
            turnSign (u a) +
              ((List.range Q).map (fun i =>
                (if (i + 1) % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (i + 1))))).sum := by
          rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
          simp [Function.comp_def]
        have hneg_sum :
            ((List.range Q).map (fun i =>
              (if (i + 1) % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (i + 1))))).sum =
            -((List.range Q).map (fun i =>
              (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (i + 1))))).sum := by
          have haux : ∀ (xs : List Nat),
              (xs.map (fun i => (if (i + 1) % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (i + 1))))).sum =
              -(xs.map (fun i => (if i % 2 = 0 then (1 : Int) else -1) * turnSign (u (a + (i + 1))))).sum := by
            intro xs
            induction xs with
            | nil => simp
            | cons x xs ixs =>
              simp only [List.map_cons, List.sum_cons, ixs]
              by_cases hx : x % 2 = 0
              · have h1 : (x + 1) % 2 ≠ 0 := by omega
                simp [hx, h1]; omega
              · have h1 : (x + 1) % 2 = 0 := by omega
                simp [hx, h1]; omega
          exact haux (List.range Q)
        have hQodd : Q % 2 ≠ 0 := by omega
        rw [hL, hR, hneg_sum, hper a]
        simp only [hQodd, ite_false]
        omega
      rw [hstep, ih]
      by_cases ha : a % 2 = 0
      · have h1 : (a + 1) % 2 ≠ 0 := by omega
        simp [ha, h1]
      · have h1 : (a + 1) % 2 = 0 := by omega
        simp [ha, h1]

/-- **Explicit checkerboard-sign shift bookkeeping (L25):** Shifting a consistent word `w` by phase
`a` preserves `(n_+, n_-)` if `a` is even and swaps `(n_+, n_-) ↦ (n_-, n_+)` if `a` is odd. -/
theorem checker_counts_shift {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (a : Nat) :
    let w' := fun i => repeatWord P w (a + i)
    let p0 := ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length
    let m0 := ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length
    let p1 := ((oddClassReps P w').filter (fun i => decide (checkerSign (wordPos w' i) = 1))).length
    let m1 := ((oddClassReps P w').filter (fun i => decide (checkerSign (wordPos w' i) = -1))).length
    (a % 2 = 0 → p1 = p0 ∧ m1 = m0) ∧
    (a % 2 = 1 → p1 = m0 ∧ m1 = p0) := by
  intro w' p0 m0 p1 m1
  obtain ⟨h', hg', _⟩ := h.growth_shift a
  have hsum0 :
      ((oddClassReps P w).map (fun i => checkerSign (wordPos w i))).sum =
      ((List.range P).map (fun i =>
        (if i % 2 = 0 then (1 : Int) else -1) * turnSign (repeatWord P w i))).sum := by
    rw [← h.sum_weighted_turnSign (fun i => checkerSign (wordPos w i))
      (fun _ _ _ _ hsc => h.checkerSign_sameClass hsc)]
    congr 1; apply List.map_congr_left
    intro i hi
    rw [checkerSign_wordPos_eq_parity w i, repeatWord_prefix w (List.mem_range.mp hi)]
  have hsum1 :
      ((oddClassReps P w').map (fun i => checkerSign (wordPos w' i))).sum =
      ((List.range P).map (fun i =>
        (if i % 2 = 0 then (1 : Int) else -1) * turnSign (repeatWord P w (a + i)))).sum := by
    rw [← h'.sum_weighted_turnSign (fun i => checkerSign (wordPos w' i))
      (fun _ _ _ _ hsc => h'.checkerSign_sameClass hsc)]
    congr 1; apply List.map_congr_left
    intro i _
    rw [checkerSign_wordPos_eq_parity w' i]
  have hper : ∀ i, repeatWord P w (i + P) = repeatWord P w i := by
    intro i; unfold repeatWord; rw [Nat.add_mod_right]
  have hshift := altSign_sum_shift_periodic h.even hper a
  rw [← hsum0, ← hsum1] at hshift
  rw [checkerSign_sum_eq_sub_counts P w, checkerSign_sum_eq_sub_counts P w'] at hshift
  have htot0 : p0 + m0 = wordGrowth P w := checkerSign_counts_sum_eq_growth P w
  have htot1 : p1 + m1 = wordGrowth P w' := checkerSign_counts_sum_eq_growth P w'
  rw [hg'] at htot1
  change (p1 : Int) - (m1 : Int) = (if a % 2 = 0 then (1 : Int) else -1) * ((p0 : Int) - (m0 : Int)) at hshift
  constructor
  · intro ha
    simp only [ha, ite_true, Int.one_mul] at hshift
    omega
  · intro ha
    have hne : a % 2 ≠ 0 := by omega
    simp only [hne, ite_false] at hshift
    omega

private theorem exists_shift_to_two_negTwo {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellDiagonalDrift (wordDrift P w)) :
    ∃ a : Nat,
      ConsistentWord P (fun i => repeatWord P w (a + i)) ∧
      wordGrowth P (fun i => repeatWord P w (a + i)) = wordGrowth P w ∧
      wordDrift P (fun i => repeatWord P w (a + i)) = (2, -2) := by
  obtain ⟨r, hr⟩ := exists_rotate_of_twoCellDiagonal hd
  obtain ⟨a, haP, hdir⟩ := UnitDiagonal.ConsistentWord.exists_phase_dir h h.pos_period r
  obtain ⟨h', hg', hd'⟩ := h.growth_shift a
  have hdir_rep : (wordTrace (repeatWord P w) a).2 = r := by
    rw [repeatWord_trace w (Nat.le_of_lt haP)]
    exact hdir
  rw [hdir_rep, ← hr, rotatePoint_inverse] at hd'
  exact ⟨a, h', hg', hd'⟩

end TwoCellDiagonal

/-! ## 3. Headline theorems (word and orbit forms) and `stdHighwaySE` Theorem C sanity check -/

/-- **Headline (L25, word form):** No consistent word with two-cell diagonal full drift
`v ∈ {(±2, ±2)}` has growth `4`. -/
theorem ConsistentWord.twoCellDiagonal_growth_ne_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellDiagonalDrift (wordDrift P w)) :
    wordGrowth P w ≠ 4 := by
  obtain ⟨_, h', hg', hd'⟩ := TwoCellDiagonal.exists_shift_to_two_negTwo h hd
  rw [← hg']
  exact TwoCellDiagonal.drift_two_negTwo_growth_ne_four h' hd'

/-- Blueprint §1.2 alias for `ConsistentWord.twoCellDiagonal_growth_ne_four`. -/
theorem ConsistentWord.not_twoCellDiagonal_of_growth_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellDiagonalDrift (wordDrift P w)) :
    wordGrowth P w ≠ 4 :=
  h.twoCellDiagonal_growth_ne_four hd

/-- **Ke Theorem C (L28, word form):** Every consistent word with two-cell diagonal full drift
`v ∈ {(±2, ±2)}` has at least `2` odd translation classes of each checkerboard sign `χ = ±1`
(and both counts are even by `TwoCellDiagonal.twoCellDiagonal_checker_counts_even`). -/
theorem ConsistentWord.twoCellDiagonal_checker_mixed {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellDiagonalDrift (wordDrift P w)) :
    2 ≤ ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length ∧
    2 ≤ ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length := by
  obtain ⟨a, h', _, hd'⟩ := TwoCellDiagonal.exists_shift_to_two_negTwo h hd
  have hmix := TwoCellDiagonal.drift_two_negTwo_checker_mixed h' hd'
  have hshift := TwoCellDiagonal.checker_counts_shift h a
  by_cases ha : a % 2 = 0
  · obtain ⟨hp, hm⟩ := hshift.1 ha
    rw [hp, hm] at hmix
    exact hmix
  · obtain ⟨hp, hm⟩ := hshift.2 (by omega)
    rw [hp, hm] at hmix
    exact ⟨hmix.2, hmix.1⟩

/-- **Headline (L25, orbit form):** No finite-support orbit with a positive periodic tail of
two-cell diagonal full drift `v ∈ {(±2, ±2)}` has growth `4`. -/
theorem periodic_tail_twoCellDiagonal_growth_ne_four {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v)
    (hv : TwoCellDiagonalDrift v) :
    wordGrowth P (fun i => readColor s (T + i)) ≠ 4 := by
  have hc := periodic_tail_consistent_at_start hs hP h
  have hd := UnitDiagonal.wordDrift_of_highway h
  have hdv : TwoCellDiagonalDrift (wordDrift P (fun i => readColor s (T + i))) := by
    rw [hd, TwoCellDiagonal.twoCellDiagonalDrift_rotatePoint]
    exact hv
  exact hc.twoCellDiagonal_growth_ne_four hdv

/-- **Ke Theorem C (L28, orbit form):** Every finite-support orbit with a positive periodic tail
of two-cell diagonal full drift `v ∈ {(±2, ±2)}` has at least `2` odd translation classes of each
checkerboard sign `χ = ±1`. -/
theorem periodic_tail_twoCellDiagonal_checker_mixed {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v)
    (hv : TwoCellDiagonalDrift v) :
    2 ≤ ((oddClassReps P (fun i => readColor s (T + i))).filter
      (fun i => decide (checkerSign (wordPos (fun i => readColor s (T + i)) i) = 1))).length ∧
    2 ≤ ((oddClassReps P (fun i => readColor s (T + i))).filter
      (fun i => decide (checkerSign (wordPos (fun i => readColor s (T + i)) i) = -1))).length := by
  have hc := periodic_tail_consistent_at_start hs hP h
  have hd := UnitDiagonal.wordDrift_of_highway h
  have hdv : TwoCellDiagonalDrift (wordDrift P (fun i => readColor s (T + i))) := by
    rw [hd, TwoCellDiagonal.twoCellDiagonalDrift_rotatePoint]
    exact hv
  exact hc.twoCellDiagonal_checker_mixed hdv

/-- Non-vacuity sanity check: `stdHighwaySE` (`g = 12`, drift `(2, -2)`) and `certifiedColor`
(`g = 12`, drift `(-2, -2)`) both satisfy `twoCellDiagonal_growth_ne_four` and Ke Theorem C
(`twoCellDiagonal_checker_mixed`), with exact counts `(4, 8)` and `(8, 4)` swapped by the odd
phase shift `a = 7`. -/
theorem stdHighwaySE_theorem_C_sanity :
    wordGrowth 104 TwoCellDiagonal.stdHighwaySE = 12 ∧
    wordGrowth 104 TwoCellDiagonal.stdHighwaySE ≠ 4 ∧
    2 ≤ ((oddClassReps 104 TwoCellDiagonal.stdHighwaySE).filter
      (fun i => decide (checkerSign (wordPos TwoCellDiagonal.stdHighwaySE i) = 1))).length ∧
    2 ≤ ((oddClassReps 104 TwoCellDiagonal.stdHighwaySE).filter
      (fun i => decide (checkerSign (wordPos TwoCellDiagonal.stdHighwaySE i) = -1))).length ∧
    2 ≤ ((oddClassReps 104 certifiedColor).filter
      (fun i => decide (checkerSign (wordPos certifiedColor i) = 1))).length ∧
    2 ≤ ((oddClassReps 104 certifiedColor).filter
      (fun i => decide (checkerSign (wordPos certifiedColor i) = -1))).length := by
  have hdSE : TwoCellDiagonalDrift (wordDrift 104 TwoCellDiagonal.stdHighwaySE) := by
    rw [TwoCellDiagonal.stdHighwaySE_drift]
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  have hdSW : TwoCellDiagonalDrift (wordDrift 104 certifiedColor) := by
    rw [Drift.standard_word_drift]
    exact ⟨Or.inr rfl, Or.inr rfl⟩
  have hmixSE := TwoCellDiagonal.stdHighwaySE_consistent.twoCellDiagonal_checker_mixed hdSE
  have hmixSW := standard_word_consistent.twoCellDiagonal_checker_mixed hdSW
  exact ⟨TwoCellDiagonal.stdHighwaySE_growth,
    TwoCellDiagonal.stdHighwaySE_consistent.twoCellDiagonal_growth_ne_four hdSE,
    hmixSE.1, hmixSE.2, hmixSW.1, hmixSW.2⟩

end LangtonsAnt
