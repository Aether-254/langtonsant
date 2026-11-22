import DriftRank
import UnitDiagonalReduction

/-!
# Periodic-tail growth definitions, mod-4 potential, residue theorem, and `g = 4` trichotomy

This module formalizes Batch 1 (definitions and lemmas L01–L13) of the periodic-tail growth
blueprint (`research/growth-blueprint-2026-11-22.md`) purely in the Lean kernel (no `sorry`,
no `axiom`, no `native_decide`).

## Contents

1. Growth definitions (`leftCount`, `rightCount`, `wordGrowthInt`, `sameClassPhases`,
   `rankZeroReps`, `oddClassReps`, `wordGrowth`, `checkerSign`, `TwoCellAxialDrift`,
   `TwoCellDiagonalDrift`) and vector characterizations.
2. List-sum, permutation, and bucket-partition helpers.
3. L01–L02: class-wise stable-rank cancellation, rank-0 class partition of `[0, P)`,
   equivalence of turn-balance growth (`#R - #L`), odd-class count (`|O|`), and net black-cell
   growth (`FiniteState.black_length_run`, `HighwayFrom.net_black_growth`).
4. L03–L06: mod-4 heading code (`4 ∣ g`, `2 ∣ P`, `2 ∣ (a + b)`, `leftCount` parity),
   checkerboard sign invariance under drift shifts, and orbit/word shift invariance of growth.
5. L07–L10: Ke's explicit mod-4 potential (`headPot` and rotated `headPotY`), telescoping
   over one period, monodromy of periodic antiderivatives, and the signed mod-4 trail residue
   identities along both `x` and `y`.
6. L11–L13: `±1` residue fiber length lower bound, strand-density bound
   `2 * max(|a|, |b|) ≤ g`, positive growth `0 < g` (`4 ≤ g`), the `g = 4` drift trichotomy
   (unit diagonal, two-cell axial, or two-cell diagonal — 12 vectors), two-cell axial checker
   balance, and two-cell diagonal `g = 4` checker-purity and lane split.
7. Kernel sanity check on the standard 104-step highway (`standard_word_growth = 12`).
-/

namespace LangtonsAnt

/-! ## 1. Growth definitions and drift predicates -/

/-- Number of black-cell reads (left turns `L`, `true`) in one period `[0, P)`. -/
def leftCount (P : Nat) (w : Nat → Bool) : Nat :=
  ((List.range P).filter (fun i => w i)).length

/-- Number of white-cell reads (right turns `R`, `false`) in one period `[0, P)`. -/
def rightCount (P : Nat) (w : Nat → Bool) : Nat :=
  ((List.range P).filter (fun i => !w i)).length

/-- Signed turn-balance growth `g_turn = #R - #L`. -/
def wordGrowthInt (P : Nat) (w : Nat → Bool) : Int :=
  (rightCount P w : Int) - (leftCount P w : Int)

/-- Single-step turn sign: `+1` on white (`false`, right turn), `-1` on black (`true`, left). -/
def turnSign (b : Bool) : Int :=
  if b then -1 else 1

/-- Modulo-4 heading code: north `0`, east `1`, south `2`, west `3`. -/
def dirCode : Direction → Int
  | .north => 0
  | .east => 1
  | .south => 2
  | .west => 3

/-- All phases in `[0, P)` belonging to the same full `wordDrift P w` translation class as `i`. -/
def sameClassPhases (P : Nat) (w : Nat → Bool) (i : Nat) : List Nat :=
  Drift.classPhases (wordDrift P w) P w (wordPos w i)

/-- Whether phase `i`'s full translation class has odd visit multiplicity. -/
def isOddClassPhase (P : Nat) (w : Nat → Bool) (i : Nat) : Bool :=
  decide ((sameClassPhases P w i).length % 2 = 1)

/-- Canonical rank-0 representative phase for each visited full translation class. -/
def rankZeroReps (P : Nat) (w : Nat → Bool) : List Nat :=
  (List.range P).filter (fun i => decide (Drift.stableRank P w i = 0))

/-- Canonical rank-0 representatives of all odd-multiplicity full translation classes (`O`). -/
def oddClassReps (P : Nat) (w : Nat → Bool) : List Nat :=
  (List.range P).filter (fun i =>
    decide (Drift.stableRank P w i = 0) && isOddClassPhase P w i)

/-- Natural-number growth `g_odd = |O|`, counting odd-multiplicity full translation classes. -/
def wordGrowth (P : Nat) (w : Nat → Bool) : Nat :=
  (oddClassReps P w).length

/-- Checkerboard parity sign `χ(x, y) = (-1)^(x + y) ∈ {1, -1}`. -/
def checkerSign (p : Point) : Int :=
  if (p.1 + p.2) % 2 = 0 then 1 else -1

/-- Two-cell axial full drift: `v ∈ {(2, 0), (-2, 0), (0, 2), (0, -2)}`. -/
def TwoCellAxialDrift (v : Point) : Prop :=
  ((v.1 = 2 ∨ v.1 = -2) ∧ v.2 = 0) ∨ (v.1 = 0 ∧ (v.2 = 2 ∨ v.2 = -2))

/-- Two-cell diagonal full drift: `v ∈ {(2, 2), (2, -2), (-2, 2), (-2, -2)}`. -/
def TwoCellDiagonalDrift (v : Point) : Prop :=
  (v.1 = 2 ∨ v.1 = -2) ∧ (v.2 = 2 ∨ v.2 = -2)

theorem unitDiagonalDrift_iff_vecs (v : Point) :
    UnitDiagonal.UnitDiagonalDrift v ↔
      v = (1, 1) ∨ v = (1, -1) ∨ v = (-1, 1) ∨ v = (-1, -1) := by
  rcases v with ⟨a, b⟩
  simp only [UnitDiagonal.UnitDiagonalDrift]
  constructor
  · rintro ⟨rfl | rfl, rfl | rfl⟩ <;> simp
  · rintro (h | h | h | h) <;> cases h <;> simp

theorem twoCellAxialDrift_iff_vecs (v : Point) :
    TwoCellAxialDrift v ↔
      v = (2, 0) ∨ v = (-2, 0) ∨ v = (0, 2) ∨ v = (0, -2) := by
  rcases v with ⟨a, b⟩
  simp only [TwoCellAxialDrift]
  constructor
  · rintro (⟨rfl | rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> simp
  · rintro (h | h | h | h) <;> cases h <;> simp

theorem twoCellDiagonalDrift_iff_vecs (v : Point) :
    TwoCellDiagonalDrift v ↔
      v = (2, 2) ∨ v = (2, -2) ∨ v = (-2, 2) ∨ v = (-2, -2) := by
  rcases v with ⟨a, b⟩
  simp only [TwoCellDiagonalDrift]
  constructor
  · rintro ⟨rfl | rfl, rfl | rfl⟩ <;> simp
  · rintro (h | h | h | h) <;> cases h <;> simp

theorem twoCellDiagonalDrift_iff_diagonalDrift (v : Point) :
    TwoCellDiagonalDrift v ↔ DiagonalDrift v :=
  Iff.rfl

/-! ## 2. List-sum, permutation, and bucketing helpers -/

private theorem int_sum_cons (a : Int) (xs : List Int) :
    (a :: xs).sum = a + xs.sum :=
  rfl

private theorem int_sum_append (xs ys : List Int) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.cons_append, int_sum_cons, ih]
    omega

private theorem int_sum_perm {xs ys : List Int} (h : xs.Perm ys) :
    xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [int_sum_cons, ih]
  | swap x y l => simp only [int_sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem int_sum_flatten (L : List (List Int)) :
    L.flatten.sum = (L.map List.sum).sum := by
  induction L with
  | nil => simp
  | cons xs L ih =>
    simp only [List.flatten_cons, int_sum_append, List.map_cons, int_sum_cons, ih]

private theorem int_sum_map_const_mul {α : Type} (c : Int) (f : α → Int) (xs : List α) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, int_sum_cons, ih, Int.mul_add]

private theorem int_sum_map_congr {α : Type} {f g : α → Int} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, int_sum_cons,
      h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem int_sum_map_ite_filter {α : Type} (p : α → Bool) (f : α → Int) (xs : List α) :
    (xs.map (fun x => if p x then f x else 0)).sum = ((xs.filter p).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx, ih]

private theorem int_sum_map_mul_indicator {α : Type} (p : α → Bool) (f : α → Int) (xs : List α) :
    (xs.map (fun x => f x * if p x then (1 : Int) else 0)).sum = ((xs.filter p).map f).sum := by
  rw [← int_sum_map_ite_filter p f xs]
  apply int_sum_map_congr
  intro x _
  cases p x <;> simp

private theorem int_sum_map_ones {α : Type} (xs : List α) :
    (xs.map (fun _ => (1 : Int))).sum = (xs.length : Int) := by
  induction xs with
  | nil => simp
  | cons _ xs ih =>
    simp only [List.map_cons, int_sum_cons, ih, List.length_cons, Int.natCast_add, Int.natCast_one]
    omega

private theorem int_sum_reverse (xs : List Int) :
    xs.reverse.sum = xs.sum :=
  int_sum_perm xs.reverse_perm

private theorem nat_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.cons_append, List.sum_cons, ih]; omega

private theorem filter_length_add_not {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx] <;> omega

private theorem int_sum_turnSign_eq_sub {α : Type} (f : α → Bool) (xs : List α) :
    (xs.map (fun x => turnSign (f x))).sum =
      ((xs.filter (fun x => !f x)).length : Int) - ((xs.filter f).length : Int) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, int_sum_cons, ih]
    cases hfx : f x <;> simp [hfx, turnSign] <;> omega

private theorem nodup_flatten_of_disjoint {α : Type} (L : List (List α))
    (hnd : ∀ xs ∈ L, xs.Nodup)
    (hdisj : L.Pairwise (fun xs ys => ∀ a, a ∈ xs → a ∉ ys)) :
    L.flatten.Nodup := by
  induction L with
  | nil => simp
  | cons xs L ih =>
    rw [List.flatten_cons, List.nodup_append]
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisj
    refine ⟨hnd xs (by simp), ih (fun ys hys => hnd ys (by simp [hys])) htail, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨ys, hys, hay⟩ := List.mem_flatten.mp hb
    exact hhead ys hys a ha hay

private theorem range_odd_filter_length (n : Nat) :
    ((List.range n).filter (fun r => decide (r % 2 = 1))).length = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases hn : n % 2 = 1
    · simp [hn]; omega
    · simp [hn]; omega

private theorem range_even_filter_length (n : Nat) :
    ((List.range n).filter (fun r => !decide (r % 2 = 1))).length = (n + 1) / 2 := by
  have hsum := filter_length_add_not (fun r => decide (r % 2 = 1)) (List.range n)
  rw [range_odd_filter_length, List.length_range] at hsum
  omega

private theorem bucket_length_sum_range {α : Type} (m : Nat) (k : α → Nat) (xs : List α)
    (hk : ∀ x ∈ xs, k x < m) :
    ((List.range m).map (fun r => (xs.filter (fun x => decide (k x = r))).length)).sum =
      xs.length := by
  induction xs with
  | nil =>
    have hz : ∀ n, ((List.range n).map (fun _ => (0 : Nat))).sum = 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn => simp [List.range_succ, ihn]
    simpa using hz m
  | cons x xs ih =>
    have hkx : k x < m := hk x (by simp)
    have hstep : ∀ n,
        ((List.range n).map (fun r =>
          ((x :: xs).filter (fun y => decide (k y = r))).length)).sum =
        ((List.range n).map (fun r =>
          (xs.filter (fun y => decide (k y = r))).length)).sum +
          if k x < n then 1 else 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [List.range_succ, List.map_append, List.map_append, nat_sum_append, nat_sum_append, ihn]
        simp only [List.map_singleton, List.sum_singleton]
        by_cases hkn : k x = n
        · subst hkn
          simp
          omega
        · have hne : decide (k x = n) = false := decide_eq_false hkn
          have hlt : (k x < n + 1) ↔ (k x < n) := by omega
          simp [hne, hlt]
          omega
    rw [hstep m, ite_eq_left hkx, ih (fun y hy => hk y (by simp [hy]))]
    simp

private theorem nat_sum_ge_of_forall_ge {α : Type} (c : Nat) (f : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, c ≤ f x) :
    c * xs.length ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    omega

private theorem range_indicator_sum (m r : Nat) (hr : r < m) :
    ((List.range m).map (fun k => if k = r then (1 : Int) else 0)).sum = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    by_cases he : m = r
    · subst he
      have hz : ((List.range m).map (fun k => if k = m then (1 : Int) else 0)).sum = 0 := by
        have h0 : ∀ xs : List Nat, (∀ k ∈ xs, k ≠ m) →
            (xs.map (fun k => if k = m then (1 : Int) else 0)).sum = 0 := by
          intro xs hne
          induction xs with
          | nil => simp
          | cons a xs ixs =>
            simp [hne a (by simp), ixs (fun k hk => hne k (by simp [hk]))]
        exact h0 (List.range m) (fun k hk => by have := List.mem_range.mp hk; omega)
      simp [hz]
    · simp [he, ih (by omega)]

private def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: xs => if a ∈ xs then dedupList xs else a :: dedupList xs

private theorem mem_dedupList {α : Type} [DecidableEq α] {a : α} {xs : List α} :
    a ∈ dedupList xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [dedupList]
  | cons x xs ih =>
    unfold dedupList
    by_cases hx : x ∈ xs
    · simp only [hx, ite_true, ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun he => he ▸ hx) id⟩
    · simp only [hx, ite_false, List.mem_cons, ih]

private theorem nodup_dedupList {α : Type} [DecidableEq α] (xs : List α) :
    (dedupList xs).Nodup := by
  induction xs with
  | nil => simp [dedupList]
  | cons x xs ih =>
    unfold dedupList
    by_cases hx : x ∈ xs
    · simp only [hx, ite_true]; exact ih
    · simp only [hx, ite_false]
      exact List.nodup_cons.mpr ⟨fun h => hx (mem_dedupList.mp h), ih⟩

/-- Grouping a `Nodup` list `xs` by a key `key : α → β` with decidable equality preserves
integer sums over `xs`. -/
private theorem int_sum_group_by_key {α β : Type} [DecidableEq β]
    (key : α → β) (f : α → Int) (xs : List α) (hnd : xs.Nodup) :
    (xs.map f).sum =
      ((dedupList (xs.map key)).map (fun b =>
        ((xs.filter (fun x => decide (key x = b))).map f).sum)).sum := by
  let keys := dedupList (xs.map key)
  have hknd : keys.Nodup := nodup_dedupList (xs.map key)
  have hpart : xs.Perm ((keys.map (fun b => xs.filter (fun x => decide (key x = b)))).flatten) := by
    apply (List.perm_ext_iff_of_nodup hnd ?_).mpr
    · intro x
      rw [List.mem_flatten]
      constructor
      · intro hx
        refine ⟨xs.filter (fun y => decide (key y = key x)), ?_, ?_⟩
        · exact List.mem_map.mpr ⟨key x,
            mem_dedupList.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩), rfl⟩
        · exact List.mem_filter.mpr ⟨hx, by simp⟩
      · rintro ⟨ys, hys, hxy⟩
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hys
        exact (List.mem_filter.mp hxy).1
    · apply nodup_flatten_of_disjoint
      · intro ys hys
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hys
        exact hnd.filter _
      · apply List.pairwise_map.mpr
        apply List.Pairwise.imp _ hknd
        intro b1 b2 hne x hx1 hx2
        have hb1 : key x = b1 := of_decide_eq_true (List.mem_filter.mp hx1).2
        have hb2 : key x = b2 := of_decide_eq_true (List.mem_filter.mp hx2).2
        exact hne (hb1.symm.trans hb2)
  have hp := int_sum_perm (hpart.map f)
  rw [hp, List.map_flatten, int_sum_flatten, List.map_map, List.map_map]
  rfl

theorem rightCount_add_leftCount (P : Nat) (w : Nat → Bool) :
    rightCount P w + leftCount P w = P := by
  have h := filter_length_add_not (fun i => w i) (List.range P)
  rw [List.length_range] at h
  unfold rightCount leftCount
  omega

theorem wordGrowthInt_eq_sum_turnSign (P : Nat) (w : Nat → Bool) :
    wordGrowthInt P w = ((List.range P).map (fun i => turnSign (w i))).sum := by
  unfold wordGrowthInt rightCount leftCount
  exact (int_sum_turnSign_eq_sub w (List.range P)).symm

/-! ## 3. L01–L02: Class-wise cancellation, rank-0 partition, and growth equivalences -/

theorem ConsistentWord.pos_period {P : Nat} {w : Nat → Bool} (h : ConsistentWord P w) :
    0 < P := by
  rcases Nat.eq_zero_or_pos P with rfl | hpos
  · exact False.elim (h.2.1 rfl)
  · exact hpos

/-- **L01 (class counts):** On any full translation class `C`, the stable-rank bijection forces
alternating white/black reads (`R, L, R, L, …`), so left/right counts are `⌊|C|/2⌋` and `⌈|C|/2⌉`,
and the signed turn sum over `C` equals `|C| mod 2`. -/
theorem ConsistentWord.class_turn_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (c : Point) :
    let C := Drift.classPhases (wordDrift P w) P w c
    (C.filter (fun i => w i)).length = C.length / 2 ∧
    (C.filter (fun i => !w i)).length = (C.length + 1) / 2 ∧
    (C.filter (fun i => !w i)).length = (C.filter (fun i => w i)).length + C.length % 2 ∧
    (C.map (fun i => turnSign (w i))).sum = (C.length % 2 : Int) := by
  intro C
  have hperm := Drift.stableRank_map_perm_range (c := c) rfl h.2.1
  have hfilt_eq :
      C.filter (fun i => w i) =
        C.filter (fun i => decide (Drift.stableRank P w i % 2 = 1)) := by
    apply List.filter_congr
    intro i hi
    exact Drift.consistentWord_stableRank_color h (Drift.mem_classPhases.mp hi).1
  have hmap_filter :
      (C.filter (fun i => decide (Drift.stableRank P w i % 2 = 1))).length =
        ((C.map (Drift.stableRank P w)).filter (fun r => decide (r % 2 = 1))).length := by
    rw [List.filter_map]
    simp only [Function.comp_def, List.length_map]
  have hleft : (C.filter (fun i => w i)).length = C.length / 2 := by
    rw [hfilt_eq, hmap_filter,
      (hperm.filter (fun r => decide (r % 2 = 1))).length_eq,
      range_odd_filter_length]
  have htot := filter_length_add_not (fun i => w i) C
  have hright : (C.filter (fun i => !w i)).length = (C.length + 1) / 2 := by omega
  have hdiff : (C.filter (fun i => !w i)).length =
      (C.filter (fun i => w i)).length + C.length % 2 := by omega
  have hsum : (C.map (fun i => turnSign (w i))).sum = (C.length % 2 : Int) := by
    rw [int_sum_turnSign_eq_sub w C, hright, hleft]
    omega
  exact ⟨hleft, hright, hdiff, hsum⟩

theorem ConsistentWord.sameClassPhases_sum_turnSign {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (i : Nat) :
    ((sameClassPhases P w i).map (fun j => turnSign (w j))).sum =
      if isOddClassPhase P w i then 1 else 0 := by
  have hsum := (h.class_turn_counts (wordPos w i)).2.2.2
  change ((sameClassPhases P w i).map (fun j => turnSign (w j))).sum =
    ((sameClassPhases P w i).length % 2 : Int) at hsum
  rw [hsum]
  unfold isOddClassPhase
  by_cases ho : (sameClassPhases P w i).length % 2 = 1
  · simp only [ho, decide_true, ite_true]
    omega
  · simp only [ho, decide_false, Bool.false_eq_true, ite_false]
    omega

theorem rankZeroReps_nodup (P : Nat) (w : Nat → Bool) :
    (rankZeroReps P w).Nodup :=
  List.nodup_range.filter _

theorem oddClassReps_nodup (P : Nat) (w : Nat → Bool) :
    (oddClassReps P w).Nodup :=
  List.nodup_range.filter _

theorem mem_rankZeroReps {P i : Nat} {w : Nat → Bool} :
    i ∈ rankZeroReps P w ↔ i < P ∧ Drift.stableRank P w i = 0 := by
  simp [rankZeroReps]

theorem mem_oddClassReps {P i : Nat} {w : Nat → Bool} :
    i ∈ oddClassReps P w ↔
      i < P ∧ Drift.stableRank P w i = 0 ∧ (sameClassPhases P w i).length % 2 = 1 := by
  simp [oddClassReps, isOddClassPhase]

theorem oddClassReps_eq_filter_rankZeroReps (P : Nat) (w : Nat → Bool) :
    oddClassReps P w = (rankZeroReps P w).filter (isOddClassPhase P w) := by
  unfold oddClassReps rankZeroReps
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  cases decide (Drift.stableRank P w i = 0) <;> cases isOddClassPhase P w i <;> rfl

/-- Distinct rank-0 representatives lie in distinct full translation classes. -/
theorem rankZeroReps_not_sameClass {P r₁ r₂ : Nat} {w : Nat → Bool}
    (hv : wordDrift P w ≠ (0, 0))
    (hr₁ : r₁ ∈ rankZeroReps P w) (hr₂ : r₂ ∈ rankZeroReps P w) (hne : r₁ ≠ r₂) :
    ¬ Drift.SameClass (wordDrift P w) (wordPos w r₁) (wordPos w r₂) := by
  intro hsc
  obtain ⟨h1P, h1r⟩ := mem_rankZeroReps.mp hr₁
  obtain ⟨h2P, h2r⟩ := mem_rankZeroReps.mp hr₂
  have hm1 : r₁ ∈ Drift.classPhases (wordDrift P w) P w (wordPos w r₁) :=
    Drift.mem_classPhases.mpr ⟨h1P, Drift.SameClass.refl _ _⟩
  have hm2 : r₂ ∈ Drift.classPhases (wordDrift P w) P w (wordPos w r₁) :=
    Drift.mem_classPhases.mpr ⟨h2P, hsc.symm⟩
  exact hne (Drift.stableRank_injective_on_class rfl hv hm1 hm2 (h1r.trans h2r.symm))

/-- Master class-partition lemma: `[0, P)` is a permutation of the disjoint union of the full
translation classes indexed by their unique rank-0 representatives `rankZeroReps P w`. -/
theorem range_perm_flatten_sameClassPhases {P : Nat} {w : Nat → Bool}
    (hv : wordDrift P w ≠ (0, 0)) :
    (List.range P).Perm
      (((rankZeroReps P w).map (fun r => sameClassPhases P w r)).flatten) := by
  have hnd : (((rankZeroReps P w).map (fun r => sameClassPhases P w r)).flatten).Nodup := by
    apply nodup_flatten_of_disjoint
    · intro xs hxs
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hxs
      exact Drift.classPhases_nodup _ _ _ _
    · apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem _ (rankZeroReps_nodup P w)
      intro r₁ r₂ hr₁ hr₂ hne i hi₁ hi₂
      have hsc1 := (Drift.mem_classPhases.mp hi₁).2
      have hsc2 := (Drift.mem_classPhases.mp hi₂).2
      exact rankZeroReps_not_sameClass hv hr₁ hr₂ hne (hsc1.symm.trans hsc2)
  apply (List.perm_ext_iff_of_nodup List.nodup_range hnd).mpr
  intro i
  rw [List.mem_range, List.mem_flatten]
  constructor
  · intro hiP
    have hmem : i ∈ Drift.classPhases (wordDrift P w) P w (wordPos w i) :=
      Drift.mem_classPhases.mpr ⟨hiP, Drift.SameClass.refl _ _⟩
    have hpos : 0 < (Drift.classPhases (wordDrift P w) P w (wordPos w i)).length :=
      List.length_pos_of_mem hmem
    obtain ⟨r, hrC, hr0⟩ := Drift.stableRank_surjective_on_class rfl hv hpos
    obtain ⟨hrP, hri⟩ := Drift.mem_classPhases.mp hrC
    refine ⟨sameClassPhases P w r, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨r, mem_rankZeroReps.mpr ⟨hrP, hr0⟩, rfl⟩
    · exact Drift.mem_classPhases.mpr ⟨hiP, hri.symm⟩
  · rintro ⟨xs, hxs, hix⟩
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hxs
    exact (Drift.mem_classPhases.mp hix).1

/-- Master class-collapsing identity: for any class-invariant weight `g : Nat → Int`, summing
`g i * turnSign (w i)` over `[0, P)` collapses to summing `g i` over `oddClassReps P w`. -/
theorem ConsistentWord.sum_weighted_turnSign {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (g : Nat → Int)
    (hg : ∀ i j, i < P → j < P →
      Drift.SameClass (wordDrift P w) (wordPos w i) (wordPos w j) → g i = g j) :
    ((List.range P).map (fun i => g i * turnSign (w i))).sum =
      ((oddClassReps P w).map g).sum := by
  have hperm := range_perm_flatten_sameClassPhases h.2.1
  rw [int_sum_perm (hperm.map (fun i => g i * turnSign (w i))),
    List.map_flatten, int_sum_flatten, List.map_map, List.map_map]
  have hclass :
      ((rankZeroReps P w).map (fun r =>
        ((sameClassPhases P w r).map (fun i => g i * turnSign (w i))).sum)).sum =
      ((rankZeroReps P w).map (fun r =>
        g r * if isOddClassPhase P w r then (1 : Int) else 0)).sum := by
    apply int_sum_map_congr
    intro r hr
    have hrP := (mem_rankZeroReps.mp hr).1
    have hconst :
        ((sameClassPhases P w r).map (fun i => g i * turnSign (w i))).sum =
          ((sameClassPhases P w r).map (fun i => g r * turnSign (w i))).sum := by
      apply int_sum_map_congr
      intro i hi
      obtain ⟨hiP, hsc⟩ := Drift.mem_classPhases.mp hi
      rw [hg i r hiP hrP hsc]
    rw [hconst, int_sum_map_const_mul, h.sameClassPhases_sum_turnSign r]
  change ((rankZeroReps P w).map (fun r =>
    ((sameClassPhases P w r).map (fun i => g i * turnSign (w i))).sum)).sum = _
  rw [hclass, int_sum_map_mul_indicator, ← oddClassReps_eq_filter_rankZeroReps]

/-- **L02 (turn-balance = odd-class count):** For every consistent word, `#R - #L = |O|`. -/
theorem ConsistentWord.growth_eq_turn_balance {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    wordGrowthInt P w = (wordGrowth P w : Int) := by
  rw [wordGrowthInt_eq_sum_turnSign]
  have h1 := h.sum_weighted_turnSign (fun _ => (1 : Int)) (fun _ _ _ _ _ => rfl)
  simp only [Int.one_mul] at h1
  rw [h1, int_sum_map_ones]
  rfl

/-- Blueprint §1.2 alias for `ConsistentWord.growth_eq_turn_balance`. -/
theorem ConsistentWord.wordGrowthInt_eq_nat {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    wordGrowthInt P w = (wordGrowth P w : Int) :=
  h.growth_eq_turn_balance

/-- Exact period decomposition `P = 2 * #L + g`. -/
theorem ConsistentWord.period_eq_two_mul_left_add_growth {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    P = 2 * leftCount P w + wordGrowth P w := by
  have hsum := rightCount_add_leftCount P w
  have hg := h.growth_eq_turn_balance
  unfold wordGrowthInt at hg
  omega

/-- Net black-cell count change for a duplicate-free `FiniteState` over a single step. -/
private theorem toggleCells_nodup {cells : List Point} (hnd : cells.Nodup) (p : Point) :
    (toggleCells cells p).Nodup := by
  unfold toggleCells
  split
  · exact hnd.filter _
  · exact List.nodup_cons.mpr ⟨‹p ∉ cells›, hnd⟩

private theorem filter_ne_length_of_nodup {α : Type} [DecidableEq α]
    {xs : List α} (hnd : xs.Nodup) {a : α} (ha : a ∈ xs) :
    (xs.filter (fun x => x != a)).length + 1 = xs.length := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hxnot, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with rfl | hmem
    · have hkeep : xs.filter (fun y => y != a) = xs := by
        apply List.filter_eq_self.mpr
        intro y hy
        simp only [bne_iff_ne]
        exact fun h => hxnot (h ▸ hy)
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false,
        hkeep, List.length_cons]
    · have hne : x ≠ a := fun h => hxnot (h ▸ hmem)
      have hbne : (x != a) = true := bne_iff_ne.mpr hne
      simp [hbne]
      have := ih hnd' hmem
      omega

theorem FiniteState.nodup_run (s : FiniteState) (hnd : s.black.Nodup) (n : Nat) :
    (s.run n).black.Nodup := by
  induction n with
  | zero => exact hnd
  | succ n ih => exact toggleCells_nodup ih (s.run n).pos

/-- **L02 (net black-cell growth on `FiniteState`):** Running `n` steps changes the black-cell
count by exactly `wordGrowthInt n (readColor s.toState) = #R - #L`. -/
theorem FiniteState.black_length_run (s : FiniteState) (hnd : s.black.Nodup) (n : Nat) :
    ((s.run n).black.length : Int) - (s.black.length : Int) =
      wordGrowthInt n (readColor s.toState) := by
  rw [wordGrowthInt_eq_sum_turnSign]
  induction n with
  | zero => simp [FiniteState.run]
  | succ n ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have hndn := s.nodup_run hnd n
    have hread : readColor s.toState n = decide ((s.run n).pos ∈ (s.run n).black) := by
      unfold readColor
      rw [← FiniteState.toState_run]
      rfl
    have hstep :
        (((s.run n).step).black.length : Int) - ((s.run n).black.length : Int) =
          turnSign (readColor s.toState n) := by
      rw [hread]
      unfold FiniteState.step toggleCells
      by_cases hm : (s.run n).pos ∈ (s.run n).black
      · simp only [hm, decide_true, ite_true, turnSign]
        have hlen := filter_ne_length_of_nodup hndn hm
        omega
      · simp only [hm, decide_false, ite_false, List.length_cons, turnSign, Bool.false_eq_true]
        omega
    change (((s.run n).step).black.length : Int) - (s.black.length : Int) = _
    omega

/-! ## 4. L03–L06: Heading mod 4, `4 ∣ g`, parity, checker sign, and shift invariance -/

/-- **L03:** Each right turn adds `+1 (mod 4)` and each left turn adds `-1 (mod 4)` to `dirCode`. -/
theorem dirCode_turn_mod_four (c : Bool) (d : Direction) :
    (dirCode (turn c d) - dirCode d) % 4 = turnSign c % 4 := by
  cases c <;> cases d <;> decide

theorem dirCode_wordTrace_mod_four (w : Nat → Bool) (n : Nat) :
    (dirCode (wordTrace w n).2) % 4 = (wordGrowthInt n w) % 4 := by
  rw [wordGrowthInt_eq_sum_turnSign]
  induction n with
  | zero => simp [wordTrace, dirCode]
  | succ n ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton, wordTrace]
    have hstep := dirCode_turn_mod_four (w n) (wordTrace w n).2
    have h1 := Int.add_emod (dirCode (wordTrace w n).2)
      (dirCode (turn (w n) (wordTrace w n).2) - dirCode (wordTrace w n).2) 4
    have h2 := Int.add_emod (((List.range n).map (fun i => turnSign (w i))).sum) (turnSign (w n)) 4
    have he : dirCode (wordTrace w n).2 +
        (dirCode (turn (w n) (wordTrace w n).2) - dirCode (wordTrace w n).2) =
        dirCode (turn (w n) (wordTrace w n).2) := by omega
    rw [he] at h1
    rw [h1, h2, ih, hstep]

/-- **L04 (growth mod 4):** Every consistent word has growth divisible by `4`. -/
theorem ConsistentWord.growth_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    wordGrowth P w % 4 = 0 := by
  have hd := dirCode_wordTrace_mod_four w P
  rw [h.1, h.growth_eq_turn_balance] at hd
  simp only [dirCode] at hd
  omega

/-- Divisibility form of `ConsistentWord.growth_mod_four`. -/
theorem ConsistentWord.four_dvd_growth {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    4 ∣ wordGrowth P w :=
  Nat.dvd_iff_mod_eq_zero.mpr h.growth_mod_four

theorem wordPos_sum_parity (w : Nat → Bool) (n : Nat) :
    ((wordPos w n).1 + (wordPos w n).2 - (n : Int)) % 2 = 0 := by
  have h := linearForm_wordPos_parity (u := w) (s1 := 1) (s2 := 1)
    (Or.inl rfl) (Or.inl rfl) n
  simpa only [linearForm, Int.one_mul] using h

/-- **L04 (drift parity):** Because `P` is even, the full drift `(a, b)` satisfies `2 ∣ (a + b)`. -/
theorem ConsistentWord.drift_sum_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    ((wordDrift P w).1 + (wordDrift P w).2) % 2 = 0 := by
  have hp := wordPos_sum_parity w P
  have he := h.even
  unfold wordDrift
  omega

/-- **L04 (`leftCount` parity):** Since `4 ∣ g`, `#L` is even iff `4 ∣ P`. -/
theorem ConsistentWord.leftCount_even_iff {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    leftCount P w % 2 = 0 ↔ P % 4 = 0 := by
  have hp := h.period_eq_two_mul_left_add_growth
  have hg := h.growth_mod_four
  omega

theorem ConsistentWord.leftCount_even_of_four_dvd {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hP4 : P % 4 = 0) :
    leftCount P w % 2 = 0 :=
  h.leftCount_even_iff.mpr hP4

/-- **L05 (checkerboard sign properties):** `checkerSign` flips on every unit move, is invariant
under quarter-turn rotation, and is invariant under any even-sum drift translation. -/
theorem checkerSign_eq_one_or_neg_one (p : Point) :
    checkerSign p = 1 ∨ checkerSign p = -1 := by
  unfold checkerSign
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem checkerSign_move (p : Point) (d : Direction) :
    checkerSign (move p d) = -checkerSign p := by
  have hparity : ∀ d : Direction,
      ((move p d).1 + (move p d).2) % 2 = 0 ↔ (p.1 + p.2) % 2 ≠ 0 := by
    intro d
    cases d <;> simp only [move] <;> omega
  unfold checkerSign
  by_cases h : (p.1 + p.2) % 2 = 0
  · have hne : ((move p d).1 + (move p d).2) % 2 ≠ 0 := fun h' => ((hparity d).mp h') h
    simp only [h, hne, ite_true, ite_false]
  · have heq : ((move p d).1 + (move p d).2) % 2 = 0 := (hparity d).mpr h
    simp only [h, heq, ite_true, ite_false]
    rfl

theorem checkerSign_rotatePoint_east (p : Point) :
    checkerSign (rotatePoint .east p) = checkerSign p := by
  unfold checkerSign rotatePoint
  split <;> split <;> omega

theorem checkerSign_add_scale_of_even {v : Point} (hv : (v.1 + v.2) % 2 = 0)
    (p : Point) (k : Int) :
    checkerSign (addPoint p (scalePoint v k)) = checkerSign p := by
  unfold checkerSign addPoint scalePoint
  have hsum : (p.1 + k * v.1) + (p.2 + k * v.2) = (p.1 + p.2) + k * (v.1 + v.2) := by
    rw [Int.mul_add]
    omega
  have hmod : ((p.1 + p.2) + k * (v.1 + v.2)) % 2 = (p.1 + p.2) % 2 := by
    rw [Int.add_emod, Int.mul_emod, hv]
    omega
  rw [hsum, hmod]

theorem ConsistentWord.checkerSign_sameClass {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) {p q : Point}
    (hsc : Drift.SameClass (wordDrift P w) p q) :
    checkerSign p = checkerSign q := by
  obtain ⟨k, rfl⟩ := hsc
  exact (checkerSign_add_scale_of_even h.drift_sum_even p k).symm

/-- Cyclic shifts of a `P`-periodic word preserve `wordGrowthInt P`. -/
theorem wordGrowthInt_shift_periodic {P : Nat} {w : Nat → Bool}
    (hper : ∀ i, w (i + P) = w i) (a : Nat) :
    wordGrowthInt P (fun i => w (a + i)) = wordGrowthInt P w := by
  rw [wordGrowthInt_eq_sum_turnSign, wordGrowthInt_eq_sum_turnSign]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos P with rfl | hP
    · simp
    · obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
      have hL :
          ((List.range (Q + 1)).map (fun i => turnSign (w (a + 1 + i)))).sum =
            ((List.range Q).map (fun i => turnSign (w (a + (i + 1))))).sum +
              turnSign (w (a + (Q + 1))) := by
        rw [List.range_succ, List.map_append, int_sum_append]
        simp only [List.map_singleton, List.sum_singleton]
        have h1 : ∀ i, a + 1 + i = a + (i + 1) := fun i => by omega
        simp only [h1]
      have hR :
          ((List.range (Q + 1)).map (fun i => turnSign (w (a + i)))).sum =
            turnSign (w a) +
              ((List.range Q).map (fun i => turnSign (w (a + (i + 1))))).sum := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, int_sum_cons]
        simp only [Nat.add_zero, Function.comp_def]
      rw [hL, hR, hper a]
      omega

/-- **L06 (orbit-level shift/rotation invariance):** Shifting the start time of a periodic tail
by `a` yields a consistent word with the same `wordGrowth` and rotated drift. -/
theorem periodic_tail_growth_shift {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) (a : Nat) :
    ConsistentWord P (fun i => readColor s (T + a + i)) ∧
    wordGrowth P (fun i => readColor s (T + a + i)) =
      wordGrowth P (fun i => readColor s (T + i)) ∧
    wordDrift P (fun i => readColor s (T + a + i)) =
      rotatePoint (inverseRotation (run s (T + a)).dir) v := by
  have hshift := UnitDiagonal.highwayFrom_shift h a
  have hc0 := periodic_tail_consistent_at_start hs hP h
  have hca := periodic_tail_consistent_at_start hs hP hshift
  have hper : ∀ i, readColor s (T + (i + P)) = readColor s (T + i) := by
    intro i
    rw [show T + (i + P) = (T + i) + P by omega]
    exact h.reads_periodic (by omega)
  have hgint :
      wordGrowthInt P (fun i => readColor s (T + a + i)) =
        wordGrowthInt P (fun i => readColor s (T + i)) := by
    have h1 := wordGrowthInt_shift_periodic (w := fun i => readColor s (T + i)) hper a
    simpa only [Nat.add_assoc] using h1
  have hgnat :
      wordGrowth P (fun i => readColor s (T + a + i)) =
        wordGrowth P (fun i => readColor s (T + i)) := by
    have e0 := hc0.growth_eq_turn_balance
    have ea := hca.growth_eq_turn_balance
    omega
  exact ⟨hca, hgnat, UnitDiagonal.wordDrift_of_highway hshift⟩

/-- Word-level cyclic shift of a consistent word preserves consistency and `wordGrowth` while
rotating the drift by the inverse heading at the shift phase. -/
theorem ConsistentWord.growth_shift {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (a : Nat) :
    ConsistentWord P (fun i => repeatWord P w (a + i)) ∧
    wordGrowth P (fun i => repeatWord P w (a + i)) = wordGrowth P w ∧
    wordDrift P (fun i => repeatWord P w (a + i)) =
      rotatePoint (inverseRotation (wordTrace (repeatWord P w) a).2) (wordDrift P w) := by
  have hP := h.pos_period
  let s := wordRealization P w
  have hs : FiniteSupport s.board := wordRealization_finite P w
  have hh : HighwayFrom s 0 P (wordDrift P w) := h.realization_highway hP
  have hreads : ∀ n, readColor s n = repeatWord P w n := h.realization_reads hP
  have hshift := periodic_tail_growth_shift hs hP hh a
  have heq0 : (fun i => readColor s (0 + i)) = repeatWord P w := by
    funext i; simpa only [Nat.zero_add] using hreads i
  have heqa : (fun i => readColor s (0 + a + i)) = (fun i => repeatWord P w (a + i)) := by
    funext i; simpa only [Nat.zero_add] using hreads (a + i)
  have hdir0 : s.dir = .north := by
    change (wordTrace (repeatWord P w) (P * (2 * P))).2 = .north
    have hd := UnitDiagonal.repeatWord_dir_period h.1 0 (2 * P)
    simpa only [Nat.zero_add, wordTrace] using hd
  have hdira : (run s a).dir = (wordTrace (repeatWord P w) a).2 := by
    have hr := UnitDiagonal.run_dir_wordTrace s 0 a
    simp only [Nat.zero_add, run_zero, hdir0, rotateDir] at hr
    rw [hr]
    exact congrArg Prod.snd (wordTrace_congr (fun i _ => hreads i))
  have hrep_growth : wordGrowth P (repeatWord P w) = wordGrowth P w := by
    have hrep : ConsistentWord P (repeatWord P w) :=
      h.congr (fun j hj => (repeatWord_prefix w hj).symm)
    have hint : wordGrowthInt P (repeatWord P w) = wordGrowthInt P w := by
      rw [wordGrowthInt_eq_sum_turnSign, wordGrowthInt_eq_sum_turnSign]
      apply int_sum_map_congr
      intro i hi
      rw [repeatWord_prefix w (List.mem_range.mp hi)]
    have e1 := hrep.growth_eq_turn_balance
    have e2 := h.growth_eq_turn_balance
    omega
  rw [heqa, heq0, Nat.zero_add, hdira, hrep_growth] at hshift
  exact hshift

/-- **L02 (net black-cell growth for arbitrary finite-support periodic tails):** On any periodic
tail, the net increase in black cells over one period `[t, t + P)` equals `wordGrowth`. -/
theorem HighwayFrom.net_black_growth {s : State} {T P t : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) (ht : T ≤ t)
    {Bt Btp : List Point} (hnd_t : Bt.Nodup) (hnd_tp : Btp.Nodup)
    (hBt : ∀ p, p ∈ Bt ↔ (run s t).board p = true)
    (hBtp : ∀ p, p ∈ Btp ↔ (run s (t + P)).board p = true) :
    (Btp.length : Int) - (Bt.length : Int) =
      (wordGrowth P (fun i => readColor s (T + i)) : Int) := by
  let fs : FiniteState := ⟨Bt, (run s t).pos, (run s t).dir⟩
  have hto : fs.toState = run s t := by
    cases hst : run s t with
    | mk board pos dir =>
      have hb : (fun p => decide (p ∈ Bt)) = board := by
        funext p
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, hBt p, hst]
      simp [fs, FiniteState.toState, hb, hst]
  have hrunP : (fs.run P).toState = run s (t + P) := by
    rw [FiniteState.toState_run, hto, ← run_add]
  have hperm : (fs.run P).black.Perm Btp := by
    apply (List.perm_ext_iff_of_nodup (fs.nodup_run hnd_t P) hnd_tp).mpr
    intro p
    rw [hBtp p, ← hrunP]
    simp [FiniteState.toState]
  have hlen := fs.black_length_run hnd_t P
  rw [hperm.length_eq, hto] at hlen
  have hread : readColor (run s t) = fun i => readColor s (T + (t - T) + i) := by
    funext i
    simp only [readColor, ← run_add]
    rw [show t + i = T + (t - T) + i by omega]
  rw [hread] at hlen
  obtain ⟨hca, hga, _⟩ := periodic_tail_growth_shift hs hP h (t - T)
  rw [hlen, hca.growth_eq_turn_balance, hga]

/-! ## 5. L07–L10: Ke's explicit mod-4 potential, monodromy, and trail residue theorem -/

/-- **L07:** Ke's explicit integer head potential along the `x`-coordinate. -/
def headPot (f S : Int → Int) (p : Point) (d : Direction) : Int :=
  let c := checkerSign p
  match d with
  | .north => -c * S p.1
  | .east  =>  c * (S p.1 - f p.1)
  | .south => -c * (S p.1 + 2 * f p.1)
  | .west  =>  c * (S p.1 + f p.1)

/-- **L07 (single-step mod-4 kernel, 16 local cases):** If `S(x+1) - S(x) = f(x) + f(x+1)`, then
every Langton's Ant transition satisfies `Δ headPot + turnSign * χ * f(x) ≡ 0 (mod 4)`. -/
theorem headPot_step {f S : Int → Int}
    (hS : ∀ x : Int, S (x + 1) - S x = f x + f (x + 1))
    (p : Point) (d : Direction) (b : Bool) :
    (headPot f S (move p (turn b d)) (turn b d) - headPot f S p d +
      turnSign b * checkerSign p * f p.1) % 4 = 0 := by
  have hplus := hS p.1
  have hminus := hS (p.1 - 1)
  rw [show p.1 - 1 + 1 = p.1 by omega] at hminus
  have hcm := checkerSign_move p (turn b d)
  have htsF : turnSign false = 1 := rfl
  have htsT : turnSign true = -1 := rfl
  rcases checkerSign_eq_one_or_neg_one p with hc | hc <;>
    cases d <;> cases b <;>
    · simp only [UnitDiagonal.turn_false_right, UnitDiagonal.turn_true_left,
        Direction.left, Direction.right, htsF, htsT] at hcm ⊢
      simp only [headPot]
      rw [hcm, hc]
      simp only [move]
      omega

/-- Quarter-turn rotated head potential along the `y`-coordinate. -/
def headPotY (f S : Int → Int) (p : Point) (d : Direction) : Int :=
  headPot f S (rotatePoint .east p) (rotateDir .east d)

theorem headPotY_step {f S : Int → Int}
    (hS : ∀ y : Int, S (y + 1) - S y = f y + f (y + 1))
    (p : Point) (d : Direction) (b : Bool) :
    (headPotY f S (move p (turn b d)) (turn b d) - headPotY f S p d +
      turnSign b * checkerSign p * f p.2) % 4 = 0 := by
  unfold headPotY
  rw [rotatePoint_move, rotateDir_turn]
  have h := headPot_step hS (rotatePoint .east p) (rotateDir .east d) b
  rw [checkerSign_rotatePoint_east] at h
  simpa only [rotatePoint] using h

private theorem headPot_telescope {f S : Int → Int}
    (hS : ∀ x : Int, S (x + 1) - S x = f x + f (x + 1))
    (w : Nat → Bool) (n : Nat) :
    (headPot f S (wordPos w n) (wordTrace w n).2 - headPot f S (0, 0) .north +
      ((List.range n).map (fun i =>
        (checkerSign (wordPos w i) * f (wordPos w i).1) * turnSign (w i))).sum) % 4 = 0 := by
  induction n with
  | zero => simp [wordPos, wordTrace]
  | succ n ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have hstep := headPot_step hS (wordPos w n) (wordTrace w n).2 (w n)
    have hcomm : (checkerSign (wordPos w n) * f (wordPos w n).1) * turnSign (w n) =
        turnSign (w n) * checkerSign (wordPos w n) * f (wordPos w n).1 := by
      rw [Int.mul_comm _ (turnSign (w n)), Int.mul_assoc]
    have hpos : wordPos w (n + 1) = move (wordPos w n) (turn (w n) (wordTrace w n).2) := rfl
    have hdir : (wordTrace w (n + 1)).2 = turn (w n) (wordTrace w n).2 := rfl
    rw [hpos, hdir, hcomm]
    omega

private theorem headPotY_telescope {f S : Int → Int}
    (hS : ∀ y : Int, S (y + 1) - S y = f y + f (y + 1))
    (w : Nat → Bool) (n : Nat) :
    (headPotY f S (wordPos w n) (wordTrace w n).2 - headPotY f S (0, 0) .north +
      ((List.range n).map (fun i =>
        (checkerSign (wordPos w i) * f (wordPos w i).2) * turnSign (w i))).sum) % 4 = 0 := by
  induction n with
  | zero => simp [wordPos, wordTrace]
  | succ n ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have hstep := headPotY_step hS (wordPos w n) (wordTrace w n).2 (w n)
    have hcomm : (checkerSign (wordPos w n) * f (wordPos w n).2) * turnSign (w n) =
        turnSign (w n) * checkerSign (wordPos w n) * f (wordPos w n).2 := by
      rw [Int.mul_comm _ (turnSign (w n)), Int.mul_assoc]
    have hpos : wordPos w (n + 1) = move (wordPos w n) (turn (w n) (wordTrace w n).2) := rfl
    have hdir : (wordTrace w (n + 1)).2 = turn (w n) (wordTrace w n).2 := rfl
    rw [hpos, hdir, hcomm]
    omega

private theorem periodic_add_mul {f : Int → Int} {a : Int}
    (hf : ∀ x : Int, f (x + a) = f x) (x k : Int) :
    f (x + k * a) = f x := by
  have hnat : ∀ n : Nat, ∀ y : Int, f (y + (n : Int) * a) = f y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      have he : y + ((n + 1 : Nat) : Int) * a = (y + (n : Int) * a) + a := by
        rw [Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul]; omega
      rw [he, hf, ih]
  by_cases hk : 0 ≤ k
  · have hc : (k.toNat : Int) = k := by omega
    rw [← hc]
    exact hnat k.toNat x
  · have hc : ((-k).toNat : Int) = -k := by omega
    have hinv := hnat (-k).toNat (x + k * a)
    have he : x + k * a + ((-k).toNat : Int) * a = x := by
      rw [hc, Int.neg_mul]; omega
    rw [he] at hinv
    exact hinv.symm

/-- **L08 (`x`-direction):** Telescoping `headPot` over one period and collapsing by translation
classes yields the mod-4 odd-class identity for any `a`-periodic `f`. -/
theorem ConsistentWord.oddClassReps_potential_x {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) {f S : Int → Int}
    (hS : ∀ x : Int, S (x + 1) - S x = f x + f (x + 1))
    (hf : ∀ x : Int, f (x + (wordDrift P w).1) = f x) :
    (((oddClassReps P w).map (fun i => checkerSign (wordPos w i) * f (wordPos w i).1)).sum -
      (S (wordDrift P w).1 - S 0)) % 4 = 0 := by
  have htel := headPot_telescope hS w P
  have hcoll := h.sum_weighted_turnSign
    (fun i => checkerSign (wordPos w i) * f (wordPos w i).1)
    (by
      intro i j _ _ hsc
      rw [h.checkerSign_sameClass hsc]
      obtain ⟨k, hk⟩ := hsc
      have hx : (wordPos w j).1 = (wordPos w i).1 + k * (wordDrift P w).1 :=
        congrArg Prod.fst hk
      rw [hx, periodic_add_mul hf])
  rw [hcoll, h.1] at htel
  have hcd : checkerSign (wordDrift P w) = 1 := by
    unfold checkerSign
    exact ite_eq_left h.drift_sum_even
  have hc0 : checkerSign (0, 0) = 1 := by decide
  change (headPot f S (wordDrift P w) .north - headPot f S (0, 0) .north + _) % 4 = 0 at htel
  simp only [headPot, hcd, hc0] at htel
  omega

/-- **L08 (`y`-direction):** Symmetric mod-4 odd-class identity for any `b`-periodic `f`. -/
theorem ConsistentWord.oddClassReps_potential_y {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) {f S : Int → Int}
    (hS : ∀ y : Int, S (y + 1) - S y = f y + f (y + 1))
    (hf : ∀ y : Int, f (y + (wordDrift P w).2) = f y) :
    (((oddClassReps P w).map (fun i => checkerSign (wordPos w i) * f (wordPos w i).2)).sum +
      (S (wordDrift P w).2 - S 0)) % 4 = 0 := by
  have htel := headPotY_telescope hS w P
  have hcoll := h.sum_weighted_turnSign
    (fun i => checkerSign (wordPos w i) * f (wordPos w i).2)
    (by
      intro i j _ _ hsc
      rw [h.checkerSign_sameClass hsc]
      obtain ⟨k, hk⟩ := hsc
      have hy : (wordPos w j).2 = (wordPos w i).2 + k * (wordDrift P w).2 :=
        congrArg Prod.snd hk
      rw [hy, periodic_add_mul hf])
  rw [hcoll, h.1] at htel
  have hcd : checkerSign (rotatePoint .east (wordDrift P w)) = 1 := by
    rw [checkerSign_rotatePoint_east]
    unfold checkerSign
    exact ite_eq_left h.drift_sum_even
  have hc0 : checkerSign (rotatePoint .east (0, 0)) = 1 := by decide
  have hfb : f (wordDrift P w).2 = f 0 := by
    simpa only [Int.zero_add] using hf 0
  change (headPotY f S (wordDrift P w) .north - headPotY f S (0, 0) .north + _) % 4 = 0 at htel
  simp only [headPotY, headPot, rotateDir, Direction.right] at htel
  rw [hcd, hc0] at htel
  simp only [rotatePoint, hfb] at htel
  omega

/-- Explicit antiderivative `S` with `S(0) = 0` and `S(x + 1) - S(x) = f(x) + f(x + 1)`. -/
def potSumPos (f : Int → Int) : Nat → Int
  | 0 => 0
  | n + 1 => potSumPos f n + f (n : Int) + f ((n + 1 : Nat) : Int)

def potSumNeg (f : Int → Int) : Nat → Int
  | 0 => 0
  | n + 1 => potSumNeg f n - f (-((n + 1 : Nat) : Int)) - f (-(n : Int))

def potSum (f : Int → Int) (x : Int) : Int :=
  if 0 ≤ x then potSumPos f x.toNat else potSumNeg f (-x).toNat

theorem potSum_zero (f : Int → Int) : potSum f 0 = 0 := by
  simp [potSum, potSumPos]

theorem potSum_step (f : Int → Int) (x : Int) :
    potSum f (x + 1) - potSum f x = f x + f (x + 1) := by
  by_cases hx : 0 ≤ x
  · have hx1 : 0 ≤ x + 1 := by omega
    have hto : (x + 1).toNat = x.toNat + 1 := by omega
    have hcast : (x.toNat : Int) = x := by omega
    have hcast1 : ((x.toNat + 1 : Nat) : Int) = x + 1 := by omega
    simp only [potSum, hx, hx1, ite_true, hto, potSumPos, hcast, hcast1]
    omega
  · by_cases hm1 : x = -1
    · subst hm1
      simp [potSum, potSumPos, potSumNeg]
      omega
    · have hx1 : ¬ 0 ≤ x + 1 := by omega
      have hto : (-x).toNat = (-(x + 1)).toNat + 1 := by omega
      have hcast : -((-(x + 1)).toNat : Int) = x + 1 := by omega
      have hcast1 : -(((-(x + 1)).toNat + 1 : Nat) : Int) = x := by omega
      simp only [potSum, hx, hx1, ite_false, hto, potSumNeg, hcast, hcast1]
      omega

theorem antideriv_sub_zero_eq_potSum {f S : Int → Int}
    (hS : ∀ x : Int, S (x + 1) - S x = f x + f (x + 1)) (x : Int) :
    S x - S 0 = potSum f x := by
  have hpos : ∀ n : Nat, S (n : Int) - S 0 = potSumPos f n := by
    intro n
    induction n with
    | zero => simp [potSumPos]
    | succ n ih =>
      have hs := hS (n : Int)
      simp only [potSumPos, Int.natCast_add, Int.natCast_one] at hs ⊢
      omega
  have hneg : ∀ n : Nat, S (-(n : Int)) - S 0 = potSumNeg f n := by
    intro n
    induction n with
    | zero => simp [potSumNeg]
    | succ n ih =>
      have hs := hS (-((n + 1 : Nat) : Int))
      have he : -((n + 1 : Nat) : Int) + 1 = -(n : Int) := by omega
      rw [he] at hs
      simp only [potSumNeg]
      omega
  unfold potSum
  by_cases hx : 0 ≤ x
  · have hc : (x.toNat : Int) = x := by omega
    simp only [hx, ite_true, ← hpos x.toNat, hc]
  · have hc : -((-x).toNat : Int) = x := by omega
    simp only [hx, ite_false, ← hneg (-x).toNat, hc]

private theorem potSumPos_eq (f : Int → Int) (k : Nat) :
    potSumPos f k =
      2 * ((List.range k).map (fun r : Nat => f (r : Int))).sum - f 0 + f (k : Int) := by
  induction k with
  | zero => simp [potSumPos]; omega
  | succ k ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton, potSumPos, ih]
    omega

private theorem potSumNeg_eq (f : Int → Int) (k : Nat) :
    potSumNeg f k =
      -(2 * ((List.range k).map (fun r : Nat => f (-((r + 1 : Nat) : Int)))).sum +
        f 0 - f (-(k : Int))) := by
  induction k with
  | zero => simp [potSumNeg]
  | succ k ih =>
    rw [List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton, potSumNeg, ih]
    omega

private theorem range_reverse_map_eq {α : Type} (m : Nat) (g : Nat → α) :
    (List.range m).map (fun r => g (m - 1 - r)) = ((List.range m).map g).reverse := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getElem_reverse]

/-- **L09 (monodromy of periodic antiderivatives):** If `f` is `a`-periodic (`a ≠ 0`), then
`(S a - S 0) mod 4 = (2 * ∑_{r < |a|} f(r)) mod 4`. -/
theorem antideriv_monodromy_mod_four {f S : Int → Int} {a : Int}
    (hS : ∀ x : Int, S (x + 1) - S x = f x + f (x + 1))
    (_ha : a ≠ 0) (hf : ∀ x : Int, f (x + a) = f x) :
    (S a - S 0) % 4 = (2 * ((List.range a.natAbs).map (fun r : Nat => f (r : Int))).sum) % 4 := by
  rw [antideriv_sub_zero_eq_potSum hS]
  have hper_abs : ∀ x : Int, f (x + (a.natAbs : Int)) = f x := by
    intro x
    by_cases hnonneg : 0 ≤ a
    · have hc : (a.natAbs : Int) = a := by omega
      rw [hc]; exact hf x
    · have hc : (a.natAbs : Int) = -a := by omega
      rw [hc]
      have h1 := hf (x - a)
      rw [show x - a + a = x by omega] at h1
      simpa only [show x + -a = x - a by omega] using h1.symm
  unfold potSum
  by_cases hnonneg : 0 ≤ a
  · have hto : a.toNat = a.natAbs := by omega
    simp only [hnonneg, ite_true, hto, potSumPos_eq]
    have hfa : f (a.natAbs : Int) = f 0 := by
      simpa only [Int.zero_add] using hper_abs 0
    rw [hfa]
    omega
  · have hto : (-a).toNat = a.natAbs := by omega
    simp only [hnonneg, ite_false, hto, potSumNeg_eq]
    have hfa : f (-(a.natAbs : Int)) = f 0 := by
      have h1 := hper_abs (-(a.natAbs : Int))
      simpa only [show -(a.natAbs : Int) + (a.natAbs : Int) = 0 by omega] using h1.symm
    have hrev :
        ((List.range a.natAbs).map (fun r : Nat => f (-((r + 1 : Nat) : Int)))).sum =
          ((List.range a.natAbs).map (fun r : Nat => f (r : Int))).sum := by
      have heq :
          ((List.range a.natAbs).map (fun r : Nat => f (-((r + 1 : Nat) : Int)))).sum =
            ((List.range a.natAbs).map (fun r : Nat => f ((a.natAbs - 1 - r : Nat) : Int))).sum := by
        apply int_sum_map_congr
        intro r hr
        have hrm := List.mem_range.mp hr
        have h1 := hper_abs (-((r + 1 : Nat) : Int))
        have he : -((r + 1 : Nat) : Int) + (a.natAbs : Int) = ((a.natAbs - 1 - r : Nat) : Int) := by
          omega
        rw [he] at h1
        exact h1.symm
      rw [heq, range_reverse_map_eq a.natAbs (fun r : Nat => f (r : Int)), int_sum_reverse]
    rw [hfa, hrev]
    omega

/-- **L10(1) (`x`-residue identity):** For `a ≠ 0` and each residue `r < |a|`, the signed
checkerboard sum of odd classes with `x ≡ r (mod |a|)` is congruent to `2 (mod 4)`. -/
theorem ConsistentWord.residue_sum_x_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (ha : (wordDrift P w).1 ≠ 0)
    {r : Nat} (hr : r < (wordDrift P w).1.natAbs) :
    (((oddClassReps P w).filter (fun i =>
        decide ((wordPos w i).1 % ((wordDrift P w).1.natAbs : Int) = (r : Int)))).map
      (fun i => checkerSign (wordPos w i))).sum % 4 = 2 := by
  let a := (wordDrift P w).1
  let m := a.natAbs
  let f : Int → Int := fun x => if x % (m : Int) = (r : Int) then 1 else 0
  have hf_per : ∀ x : Int, f (x + a) = f x := by
    intro x
    have hmod : (x + a) % (m : Int) = x % (m : Int) := by
      by_cases hnonneg : 0 ≤ a
      · have hc : a = 1 * (m : Int) := by dsimp [m]; omega
        rw [hc]; exact Int.add_mul_emod_self_right x 1 (m : Int)
      · have hc : a = (-1) * (m : Int) := by dsimp [m]; omega
        rw [hc]; exact Int.add_mul_emod_self_right x (-1) (m : Int)
    simp only [f, hmod]
  have hpot := h.oddClassReps_potential_x (f := f) (S := potSum f) (potSum_step f) hf_per
  have hmono := antideriv_monodromy_mod_four (potSum_step f) ha hf_per
  have hsum1 : ((List.range m).map (fun k : Nat => f (k : Int))).sum = 1 := by
    have hcongr :
        ((List.range m).map (fun k : Nat => f (k : Int))).sum =
          ((List.range m).map (fun k => if k = r then (1 : Int) else 0)).sum := by
      apply int_sum_map_congr
      intro k hk
      have hkm := List.mem_range.mp hk
      have hmod : (k : Int) % (m : Int) = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [f, hmod]
      by_cases hkr : k = r
      · subst hkr; simp
      · have hne : (k : Int) ≠ (r : Int) := by omega
        simp [hkr, hne]
    rw [hcongr]
    exact range_indicator_sum m r hr
  rw [potSum_zero, Int.sub_zero] at hpot hmono
  change (potSum f a) % 4 = (2 * ((List.range m).map (fun k : Nat => f (k : Int))).sum) % 4 at hmono
  rw [hsum1] at hmono
  have hfilt :
      ((oddClassReps P w).map (fun i => checkerSign (wordPos w i) * f (wordPos w i).1)).sum =
        (((oddClassReps P w).filter (fun i =>
            decide ((wordPos w i).1 % (m : Int) = (r : Int)))).map
          (fun i => checkerSign (wordPos w i))).sum := by
    rw [← int_sum_map_mul_indicator]
    apply int_sum_map_congr
    intro i _
    by_cases hmod : (wordPos w i).1 % (m : Int) = (r : Int)
    · simp [f, hmod]
    · simp [f, hmod]
  rw [hfilt] at hpot
  dsimp only [a, m] at hpot hmono
  omega

/-- **L10(2) (exact column conservation when `a = 0`):** Every vertical column has signed
checkerboard sum of odd classes congruent to `0 (mod 4)`. -/
theorem ConsistentWord.exact_col_sum_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (ha : (wordDrift P w).1 = 0) (x0 : Int) :
    (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 = x0))).map
      (fun i => checkerSign (wordPos w i))).sum % 4 = 0 := by
  let f : Int → Int := fun x => if x = x0 then 1 else 0
  have hf_per : ∀ x : Int, f (x + (wordDrift P w).1) = f x := by
    intro x; simp [ha]
  have hpot := h.oddClassReps_potential_x (f := f) (S := potSum f) (potSum_step f) hf_per
  rw [ha, Int.sub_self, Int.sub_zero] at hpot
  have hfilt :
      ((oddClassReps P w).map (fun i => checkerSign (wordPos w i) * f (wordPos w i).1)).sum =
        (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 = x0))).map
          (fun i => checkerSign (wordPos w i))).sum := by
    rw [← int_sum_map_mul_indicator]
    apply int_sum_map_congr
    intro i _
    by_cases hx : (wordPos w i).1 = x0 <;> simp [f, hx]
  rwa [hfilt] at hpot

/-- **L10(3a) (`y`-residue identity):** For `b ≠ 0` and each residue `r < |b|`, the signed
checkerboard sum of odd classes with `y ≡ r (mod |b|)` is congruent to `2 (mod 4)`. -/
theorem ConsistentWord.residue_sum_y_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hb : (wordDrift P w).2 ≠ 0)
    {r : Nat} (hr : r < (wordDrift P w).2.natAbs) :
    (((oddClassReps P w).filter (fun i =>
        decide ((wordPos w i).2 % ((wordDrift P w).2.natAbs : Int) = (r : Int)))).map
      (fun i => checkerSign (wordPos w i))).sum % 4 = 2 := by
  let b := (wordDrift P w).2
  let m := b.natAbs
  let f : Int → Int := fun y => if y % (m : Int) = (r : Int) then 1 else 0
  have hf_per : ∀ y : Int, f (y + b) = f y := by
    intro y
    have hmod : (y + b) % (m : Int) = y % (m : Int) := by
      by_cases hnonneg : 0 ≤ b
      · have hc : b = 1 * (m : Int) := by dsimp [m]; omega
        rw [hc]; exact Int.add_mul_emod_self_right y 1 (m : Int)
      · have hc : b = (-1) * (m : Int) := by dsimp [m]; omega
        rw [hc]; exact Int.add_mul_emod_self_right y (-1) (m : Int)
    simp only [f, hmod]
  have hpot := h.oddClassReps_potential_y (f := f) (S := potSum f) (potSum_step f) hf_per
  have hmono := antideriv_monodromy_mod_four (potSum_step f) hb hf_per
  have hsum1 : ((List.range m).map (fun k : Nat => f (k : Int))).sum = 1 := by
    have hcongr :
        ((List.range m).map (fun k : Nat => f (k : Int))).sum =
          ((List.range m).map (fun k => if k = r then (1 : Int) else 0)).sum := by
      apply int_sum_map_congr
      intro k hk
      have hkm := List.mem_range.mp hk
      have hmod : (k : Int) % (m : Int) = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [f, hmod]
      by_cases hkr : k = r
      · subst hkr; simp
      · have hne : (k : Int) ≠ (r : Int) := by omega
        simp [hkr, hne]
    rw [hcongr]
    exact range_indicator_sum m r hr
  rw [potSum_zero, Int.sub_zero] at hpot hmono
  change (potSum f b) % 4 = (2 * ((List.range m).map (fun k : Nat => f (k : Int))).sum) % 4 at hmono
  rw [hsum1] at hmono
  have hfilt :
      ((oddClassReps P w).map (fun i => checkerSign (wordPos w i) * f (wordPos w i).2)).sum =
        (((oddClassReps P w).filter (fun i =>
            decide ((wordPos w i).2 % (m : Int) = (r : Int)))).map
          (fun i => checkerSign (wordPos w i))).sum := by
    rw [← int_sum_map_mul_indicator]
    apply int_sum_map_congr
    intro i _
    by_cases hmod : (wordPos w i).2 % (m : Int) = (r : Int)
    · simp [f, hmod]
    · simp [f, hmod]
  rw [hfilt] at hpot
  dsimp only [b, m] at hpot hmono
  omega

/-- **L10(3b) (exact row conservation when `b = 0`):** Every horizontal row has signed
checkerboard sum of odd classes congruent to `0 (mod 4)`. -/
theorem ConsistentWord.exact_row_sum_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hb : (wordDrift P w).2 = 0) (y0 : Int) :
    (((oddClassReps P w).filter (fun i => decide ((wordPos w i).2 = y0))).map
      (fun i => checkerSign (wordPos w i))).sum % 4 = 0 := by
  let f : Int → Int := fun y => if y = y0 then 1 else 0
  have hf_per : ∀ y : Int, f (y + (wordDrift P w).2) = f y := by
    intro y; simp [hb]
  have hpot := h.oddClassReps_potential_y (f := f) (S := potSum f) (potSum_step f) hf_per
  rw [hb, Int.sub_self, Int.add_zero] at hpot
  have hfilt :
      ((oddClassReps P w).map (fun i => checkerSign (wordPos w i) * f (wordPos w i).2)).sum =
        (((oddClassReps P w).filter (fun i => decide ((wordPos w i).2 = y0))).map
          (fun i => checkerSign (wordPos w i))).sum := by
    rw [← int_sum_map_mul_indicator]
    apply int_sum_map_congr
    intro i _
    by_cases hy : (wordPos w i).2 = y0 <;> simp [f, hy]
  rwa [hfilt] at hpot

/-! ## 6. L11–L13: Strand-density bound, `0 < g`, `g = 4` trichotomy, and two-cell structure -/

private theorem unitSign_list_sum_parity {xs : List Int} (h : ∀ c ∈ xs, c = 1 ∨ c = -1) :
    xs.sum % 2 = (xs.length : Int) % 2 := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    have hc := h c (by simp)
    have hxs := ih (fun x hx => h x (by simp [hx]))
    simp only [int_sum_cons, List.length_cons, Int.natCast_add, Int.natCast_one]
    rcases hc with rfl | rfl <;> omega

private theorem unitSign_list_sum_bounds {xs : List Int} (h : ∀ c ∈ xs, c = 1 ∨ c = -1) :
    -(xs.length : Int) ≤ xs.sum ∧ xs.sum ≤ (xs.length : Int) := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    have hc := h c (by simp)
    have hxs := ih (fun x hx => h x (by simp [hx]))
    simp only [int_sum_cons, List.length_cons, Int.natCast_add, Int.natCast_one]
    rcases hc with rfl | rfl <;> omega

/-- **L11(1):** A list of `±1`s whose sum is `2 (mod 4)` has positive even length (`≥ 2`). -/
theorem unitSign_list_mod_four_eq_two {xs : List Int}
    (h : ∀ c ∈ xs, c = 1 ∨ c = -1) (hsum : xs.sum % 4 = 2) :
    2 ≤ xs.length ∧ xs.length % 2 = 0 := by
  have hpar := unitSign_list_sum_parity h
  have hne : xs.length ≠ 0 := by
    intro hz
    cases xs with
    | nil => simp at hsum
    | cons _ _ => simp at hz
  omega

/-- **L11(2):** A two-element list of `±1`s with sum `2 (mod 4)` has both entries equal. -/
theorem unitSign_list_length_two_of_mod_four_eq_two {xs : List Int}
    (h : ∀ c ∈ xs, c = 1 ∨ c = -1) (hsum : xs.sum % 4 = 2) (hlen : xs.length = 2) :
    xs = [1, 1] ∨ xs = [-1, -1] := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · have ha := h a (by simp)
    have hb := h b (by simp)
    simp only [List.sum_cons, List.sum_nil, Int.add_zero] at hsum
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hsum ⊢
  · simp at hlen

/-- **L12 (`x`-strand bound):** `2 * |a| ≤ wordGrowth P w`. -/
theorem ConsistentWord.two_mul_driftX_le_growth {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    2 * (wordDrift P w).1.natAbs ≤ wordGrowth P w := by
  by_cases ha : (wordDrift P w).1 = 0
  · simp [ha]
  · let m := (wordDrift P w).1.natAbs
    have hm : 0 < m := Int.natAbs_pos.mpr ha
    let key : Nat → Nat := fun i => ((wordPos w i).1 % (m : Int)).toNat
    have hkey_lt : ∀ i ∈ oddClassReps P w, key i < m := by
      intro i _
      have h0 : 0 ≤ (wordPos w i).1 % (m : Int) := Int.emod_nonneg _ (by omega)
      have hlt : (wordPos w i).1 % (m : Int) < (m : Int) := Int.emod_lt_of_pos _ (by omega)
      dsimp [key]; omega
    have hpart := bucket_length_sum_range m key (oddClassReps P w) hkey_lt
    have hge : 2 * (List.range m).length ≤
        ((List.range m).map (fun r =>
          ((oddClassReps P w).filter (fun i => decide (key i = r))).length)).sum := by
      apply nat_sum_ge_of_forall_ge
      intro r hr
      have hrm := List.mem_range.mp hr
      have hres := h.residue_sum_x_mod_four ha hrm
      have hfilt_eq :
          (oddClassReps P w).filter (fun i => decide (key i = r)) =
            (oddClassReps P w).filter (fun i =>
              decide ((wordPos w i).1 % (m : Int) = (r : Int))) := by
        apply List.filter_congr
        intro i _
        have h0 : 0 ≤ (wordPos w i).1 % (m : Int) := Int.emod_nonneg _ (by omega)
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, key]
        omega
      rw [hfilt_eq]
      have h2 := (unitSign_list_mod_four_eq_two
        (xs := ((oddClassReps P w).filter (fun i =>
            decide ((wordPos w i).1 % (m : Int) = (r : Int)))).map
          (fun i => checkerSign (wordPos w i)))
        (by
          intro c hc
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
          exact checkerSign_eq_one_or_neg_one _)
        hres).1
      simpa only [List.length_map] using h2
    rw [List.length_range, hpart] at hge
    exact hge

/-- **L12 (`y`-strand bound):** `2 * |b| ≤ wordGrowth P w`. -/
theorem ConsistentWord.two_mul_driftY_le_growth {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    2 * (wordDrift P w).2.natAbs ≤ wordGrowth P w := by
  by_cases hb : (wordDrift P w).2 = 0
  · simp [hb]
  · let m := (wordDrift P w).2.natAbs
    have hm : 0 < m := Int.natAbs_pos.mpr hb
    let key : Nat → Nat := fun i => ((wordPos w i).2 % (m : Int)).toNat
    have hkey_lt : ∀ i ∈ oddClassReps P w, key i < m := by
      intro i _
      have h0 : 0 ≤ (wordPos w i).2 % (m : Int) := Int.emod_nonneg _ (by omega)
      have hlt : (wordPos w i).2 % (m : Int) < (m : Int) := Int.emod_lt_of_pos _ (by omega)
      dsimp [key]; omega
    have hpart := bucket_length_sum_range m key (oddClassReps P w) hkey_lt
    have hge : 2 * (List.range m).length ≤
        ((List.range m).map (fun r =>
          ((oddClassReps P w).filter (fun i => decide (key i = r))).length)).sum := by
      apply nat_sum_ge_of_forall_ge
      intro r hr
      have hrm := List.mem_range.mp hr
      have hres := h.residue_sum_y_mod_four hb hrm
      have hfilt_eq :
          (oddClassReps P w).filter (fun i => decide (key i = r)) =
            (oddClassReps P w).filter (fun i =>
              decide ((wordPos w i).2 % (m : Int) = (r : Int))) := by
        apply List.filter_congr
        intro i _
        have h0 : 0 ≤ (wordPos w i).2 % (m : Int) := Int.emod_nonneg _ (by omega)
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, key]
        omega
      rw [hfilt_eq]
      have h2 := (unitSign_list_mod_four_eq_two
        (xs := ((oddClassReps P w).filter (fun i =>
            decide ((wordPos w i).2 % (m : Int) = (r : Int)))).map
          (fun i => checkerSign (wordPos w i)))
        (by
          intro c hc
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
          exact checkerSign_eq_one_or_neg_one _)
        hres).1
      simpa only [List.length_map] using h2
    rw [List.length_range, hpart] at hge
    exact hge

/-- **L12 (strand-density bound):** `2 * max(|a|, |b|) ≤ g` for full drift `(a, b)`. -/
theorem ConsistentWord.two_mul_driftInf_le_growth {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    2 * max (wordDrift P w).1.natAbs (wordDrift P w).2.natAbs ≤ wordGrowth P w := by
  have hx := h.two_mul_driftX_le_growth
  have hy := h.two_mul_driftY_le_growth
  omega

/-- **L12 (positive growth):** Every consistent word has strictly positive growth (`0 < g`). -/
theorem ConsistentWord.growth_pos {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    0 < wordGrowth P w := by
  have hbound := h.two_mul_driftInf_le_growth
  have hv := h.2.1
  by_cases hx : (wordDrift P w).1 = 0
  · have hy : (wordDrift P w).2 ≠ 0 := fun h0 => hv (Prod.ext hx h0)
    have : 0 < (wordDrift P w).2.natAbs := Int.natAbs_pos.mpr hy
    omega
  · have : 0 < (wordDrift P w).1.natAbs := Int.natAbs_pos.mpr hx
    omega

/-- **L12 (`4 ≤ g`):** Combining `4 ∣ g` and `0 < g` immediately yields `4 ≤ g`. -/
theorem ConsistentWord.four_le_growth {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    4 ≤ wordGrowth P w := by
  have hpos := h.growth_pos
  have hmod := h.growth_mod_four
  omega

private theorem driftInf_rotatePoint (r : Direction) (v : Point) :
    max (rotatePoint r v).1.natAbs (rotatePoint r v).2.natAbs =
      max v.1.natAbs v.2.natAbs := by
  cases r <;> simp [rotatePoint] <;> omega

/-- Orbit-level strand-density bound and `4 ≤ g` for any finite-support periodic tail. -/
theorem periodic_tail_growth_bounds {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    wordGrowth P (fun i => readColor s (T + i)) % 4 = 0 ∧
    2 * max v.1.natAbs v.2.natAbs ≤ wordGrowth P (fun i => readColor s (T + i)) ∧
    4 ≤ wordGrowth P (fun i => readColor s (T + i)) := by
  have hc := periodic_tail_consistent_at_start hs hP h
  have hd := UnitDiagonal.wordDrift_of_highway h
  have hinf := hc.two_mul_driftInf_le_growth
  rw [hd, driftInf_rotatePoint] at hinf
  exact ⟨hc.growth_mod_four, hinf, hc.four_le_growth⟩

/-- **L13(1) (`g = 4` drift trichotomy):** If a consistent word has growth `g = 4`, then its full
drift is one of the 12 vectors in `UnitDiagonalDrift ∪ TwoCellAxialDrift ∪ TwoCellDiagonalDrift`:
`{(±1, ±1), (±2, 0), (0, ±2), (±2, ±2)}`. -/
theorem ConsistentWord.growth_four_drift_trichotomy {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hg : wordGrowth P w = 4) :
    UnitDiagonal.UnitDiagonalDrift (wordDrift P w) ∨
    TwoCellAxialDrift (wordDrift P w) ∨
    TwoCellDiagonalDrift (wordDrift P w) := by
  have hbound := h.two_mul_driftInf_le_growth
  have heven := h.drift_sum_even
  have hne := h.2.1
  rcases hv : wordDrift P w with ⟨a, b⟩
  rw [hv, hg] at hbound
  rw [hv] at heven hne
  have ha : -2 ≤ a ∧ a ≤ 2 := by omega
  have hb : -2 ≤ b ∧ b ≤ 2 := by omega
  unfold UnitDiagonal.UnitDiagonalDrift TwoCellAxialDrift TwoCellDiagonalDrift
  have hnot0 : a ≠ 0 ∨ b ≠ 0 := by
    by_cases h0 : a = 0
    · exact Or.inr (fun hb0 => hne (Prod.ext h0 hb0))
    · exact Or.inl h0
  omega

/-- Explicit 12-vector list form of the `g = 4` drift trichotomy. -/
theorem ConsistentWord.growth_four_drift_vectors {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hg : wordGrowth P w = 4) :
    (wordDrift P w = (1, 1) ∨ wordDrift P w = (1, -1) ∨
      wordDrift P w = (-1, 1) ∨ wordDrift P w = (-1, -1)) ∨
    (wordDrift P w = (2, 0) ∨ wordDrift P w = (-2, 0) ∨
      wordDrift P w = (0, 2) ∨ wordDrift P w = (0, -2)) ∨
    (wordDrift P w = (2, 2) ∨ wordDrift P w = (2, -2) ∨
      wordDrift P w = (-2, 2) ∨ wordDrift P w = (-2, -2)) := by
  rcases h.growth_four_drift_trichotomy hg with hu | ha | hd
  · exact Or.inl ((unitDiagonalDrift_iff_vecs _).mp hu)
  · exact Or.inr (Or.inl ((twoCellAxialDrift_iff_vecs _).mp ha))
  · exact Or.inr (Or.inr ((twoCellDiagonalDrift_iff_vecs _).mp hd))

private theorem filter_length_le_two_of_parity_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    (coord : α → Int)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, coord a % 2 = coord b % 2 → a = b) :
    xs.length ≤ 2 := by
  have hsub : (xs.map (fun a => (coord a % 2).toNat)).Nodup := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      obtain ⟨hanot, hnd'⟩ := List.nodup_cons.mp hnd
      apply List.nodup_cons.mpr
      refine ⟨?_, ih hnd' (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))⟩
      intro hmem
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
      have h0a : 0 ≤ coord a % 2 := Int.emod_nonneg _ (by decide)
      have h0b : 0 ≤ coord b % 2 := Int.emod_nonneg _ (by decide)
      have hpar : coord b % 2 = coord a % 2 := by
        rw [← Int.toNat_of_nonneg h0b, ← Int.toNat_of_nonneg h0a, he]
      have hba := hinj b (by simp [hb]) a (by simp) hpar
      subst hba
      exact hanot hb
  have hinc : xs.map (fun a => (coord a % 2).toNat) ⊆ List.range 2 := by
    intro r hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
    exact List.mem_range.mpr (by omega)
  have hle := hsub.length_le_of_subset hinc
  simpa only [List.length_map, List.length_range] using hle

/-- **L13(2) (two-cell axial checkerboard balance, arbitrary growth `g`):** For any two-cell axial
drift `v ∈ {(±2, 0), (0, ±2)}`, every row (or column) has at most two odd classes and signed sum
`0`, hence the total signed checkerboard sum over `oddClassReps P w` is `0`. -/
theorem ConsistentWord.twoCellAxial_checker_sum_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hax : TwoCellAxialDrift (wordDrift P w)) :
    ((oddClassReps P w).map (fun i => checkerSign (wordPos w i))).sum = 0 := by
  rcases hax with ⟨ha, hb0⟩ | ⟨ha0, hb⟩
  · rw [int_sum_group_by_key (fun i => (wordPos w i).2) (fun i => checkerSign (wordPos w i))
      (oddClassReps P w) (oddClassReps_nodup P w)]
    have hzero : ∀ y0 : Int,
        (((oddClassReps P w).filter (fun i => decide ((wordPos w i).2 = y0))).map
          (fun i => checkerSign (wordPos w i))).sum = 0 := by
      intro y0
      let row := (oddClassReps P w).filter (fun i => decide ((wordPos w i).2 = y0))
      have hmod := h.exact_row_sum_mod_four hb0 y0
      have hlen : row.length ≤ 2 := by
        apply filter_length_le_two_of_parity_inj ((oddClassReps_nodup P w).filter _)
          (fun i => (wordPos w i).1)
        intro i hi j hj hpar
        obtain ⟨hiO, hiy⟩ := List.mem_filter.mp hi
        obtain ⟨hjO, hjy⟩ := List.mem_filter.mp hj
        have hiy' : (wordPos w i).2 = y0 := of_decide_eq_true hiy
        have hjy' : (wordPos w j).2 = y0 := of_decide_eq_true hjy
        have hsc : Drift.SameClass (wordDrift P w) (wordPos w i) (wordPos w j) := by
          rcases ha with ha2 | ha2
          · refine ⟨((wordPos w j).1 - (wordPos w i).1) / 2, ?_⟩
            apply Prod.ext <;> simp only [addPoint, scalePoint, ha2, hb0] <;> omega
          · refine ⟨-((wordPos w j).1 - (wordPos w i).1) / 2, ?_⟩
            apply Prod.ext <;> simp only [addPoint, scalePoint, ha2, hb0] <;> omega
        by_cases hne : i = j
        · exact hne
        · exact False.elim (rankZeroReps_not_sameClass h.2.1
            (mem_rankZeroReps.mpr ⟨(mem_oddClassReps.mp hiO).1, (mem_oddClassReps.mp hiO).2.1⟩)
            (mem_rankZeroReps.mpr ⟨(mem_oddClassReps.mp hjO).1, (mem_oddClassReps.mp hjO).2.1⟩)
            hne hsc)
      have hbd := unitSign_list_sum_bounds
        (xs := row.map (fun i => checkerSign (wordPos w i)))
        (by
          intro c hc
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
          exact checkerSign_eq_one_or_neg_one _)
      simp only [List.length_map] at hbd
      dsimp [row] at hlen hbd
      omega
    have hall0 : ∀ ys : List Int,
        (ys.map (fun y0 =>
          (((oddClassReps P w).filter (fun i => decide ((wordPos w i).2 = y0))).map
            (fun i => checkerSign (wordPos w i))).sum)).sum = 0 := by
      intro ys
      induction ys with
      | nil => simp
      | cons y ys iys => simp [hzero y, iys]
    exact hall0 _
  · rw [int_sum_group_by_key (fun i => (wordPos w i).1) (fun i => checkerSign (wordPos w i))
      (oddClassReps P w) (oddClassReps_nodup P w)]
    have hzero : ∀ x0 : Int,
        (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 = x0))).map
          (fun i => checkerSign (wordPos w i))).sum = 0 := by
      intro x0
      let col := (oddClassReps P w).filter (fun i => decide ((wordPos w i).1 = x0))
      have hmod := h.exact_col_sum_mod_four ha0 x0
      have hlen : col.length ≤ 2 := by
        apply filter_length_le_two_of_parity_inj ((oddClassReps_nodup P w).filter _)
          (fun i => (wordPos w i).2)
        intro i hi j hj hpar
        obtain ⟨hiO, hix⟩ := List.mem_filter.mp hi
        obtain ⟨hjO, hjx⟩ := List.mem_filter.mp hj
        have hix' : (wordPos w i).1 = x0 := of_decide_eq_true hix
        have hjx' : (wordPos w j).1 = x0 := of_decide_eq_true hjx
        have hsc : Drift.SameClass (wordDrift P w) (wordPos w i) (wordPos w j) := by
          rcases hb with hb2 | hb2
          · refine ⟨((wordPos w j).2 - (wordPos w i).2) / 2, ?_⟩
            apply Prod.ext <;> simp only [addPoint, scalePoint, ha0, hb2] <;> omega
          · refine ⟨-((wordPos w j).2 - (wordPos w i).2) / 2, ?_⟩
            apply Prod.ext <;> simp only [addPoint, scalePoint, ha0, hb2] <;> omega
        by_cases hne : i = j
        · exact hne
        · exact False.elim (rankZeroReps_not_sameClass h.2.1
            (mem_rankZeroReps.mpr ⟨(mem_oddClassReps.mp hiO).1, (mem_oddClassReps.mp hiO).2.1⟩)
            (mem_rankZeroReps.mpr ⟨(mem_oddClassReps.mp hjO).1, (mem_oddClassReps.mp hjO).2.1⟩)
            hne hsc)
      have hbd := unitSign_list_sum_bounds
        (xs := col.map (fun i => checkerSign (wordPos w i)))
        (by
          intro c hc
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
          exact checkerSign_eq_one_or_neg_one _)
      simp only [List.length_map] at hbd
      dsimp [col] at hlen hbd
      omega
    have hall0 : ∀ xs : List Int,
        (xs.map (fun x0 =>
          (((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 = x0))).map
            (fun i => checkerSign (wordPos w i))).sum)).sum = 0 := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ixs => simp [hzero x, ixs]
    exact hall0 _

private theorem checkerSign_sum_eq_sub {α : Type} (pos : α → Point) (xs : List α) :
    (xs.map (fun x => checkerSign (pos x))).sum =
      ((xs.filter (fun x => decide (checkerSign (pos x) = 1))).length : Int) -
      ((xs.filter (fun x => decide (checkerSign (pos x) = -1))).length : Int) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases checkerSign_eq_one_or_neg_one (pos x) with hx | hx <;>
      simp [hx, ih] <;> omega

private theorem checkerSign_counts_add {α : Type} (pos : α → Point) (xs : List α) :
    (xs.filter (fun x => decide (checkerSign (pos x) = 1))).length +
    (xs.filter (fun x => decide (checkerSign (pos x) = -1))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases checkerSign_eq_one_or_neg_one (pos x) with hx | hx <;> simp [hx] <;> omega

/-- **L13(2) (exact `g/2` split):** For any two-cell axial drift (in particular `(2, 0)`),
exactly `g / 2` odd classes have `χ = +1` (even checkerboard / `Q`) and `g / 2` have `χ = -1`
(odd checkerboard / `C`). -/
theorem ConsistentWord.twoCellAxial_checker_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hax : TwoCellAxialDrift (wordDrift P w)) :
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length =
      wordGrowth P w / 2 ∧
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length =
      wordGrowth P w / 2 := by
  have hsum := h.twoCellAxial_checker_sum_zero hax
  rw [checkerSign_sum_eq_sub (wordPos w)] at hsum
  have htot := checkerSign_counts_add (wordPos w) (oddClassReps P w)
  have hmod := h.growth_mod_four
  unfold wordGrowth
  unfold wordGrowth at hmod
  omega

theorem ConsistentWord.drift_two_zero_checker_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, 0)) :
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length =
      wordGrowth P w / 2 ∧
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length =
      wordGrowth P w / 2 :=
  h.twoCellAxial_checker_counts (Or.inl ⟨Or.inl (by simp [hd]), by simp [hd]⟩)

theorem ConsistentWord.drift_two_zero_growth_four_checker_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, 0)) (hg : wordGrowth P w = 4) :
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = 1))).length = 2 ∧
    ((oddClassReps P w).filter (fun i => decide (checkerSign (wordPos w i) = -1))).length = 2 := by
  simpa [hg] using h.drift_two_zero_checker_counts hd

private theorem forall_checkerSign_of_map_eq_pair {α : Type} (pos : α → Point) {xs : List α}
    {s : Int} (h : xs.map (fun x => checkerSign (pos x)) = [s, s]) :
    ∀ x ∈ xs, checkerSign (pos x) = s := by
  intro x hx
  have hm : checkerSign (pos x) ∈ xs.map (fun y => checkerSign (pos y)) :=
    List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [h] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> rfl

/-- **L13(3) (two-cell diagonal `g = 4` residue structure):** For any two-cell diagonal drift
(in particular `(2, -2)`) with `g = 4`, all four odd classes have the same checkerboard sign
(all `+1` or all `-1`), and the two `x mod 2` lanes each contain exactly `2` odd classes. -/
theorem ConsistentWord.twoCellDiagonal_growth_four_structure {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellDiagonalDrift (wordDrift P w))
    (hg : wordGrowth P w = 4) :
    ((∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = 1) ∨
      (∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = -1)) ∧
    ((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 0))).length = 2 ∧
    ((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 1))).length = 2 := by
  obtain ⟨ha, hb⟩ := hd
  have ha_ne : (wordDrift P w).1 ≠ 0 := by rcases ha with ha | ha <;> omega
  have hb_ne : (wordDrift P w).2 ≠ 0 := by rcases hb with hb | hb <;> omega
  have ha_abs : (wordDrift P w).1.natAbs = 2 := by rcases ha with ha | ha <;> omega
  have hb_abs : (wordDrift P w).2.natAbs = 2 := by rcases hb with hb | hb <;> omega
  let O := oddClassReps P w
  let Ox0 := O.filter (fun i => decide ((wordPos w i).1 % 2 = 0))
  let Ox1 := O.filter (fun i => decide ((wordPos w i).1 % 2 = 1))
  let Oy0 := O.filter (fun i => decide ((wordPos w i).2 % 2 = 0))
  have hrx0 : (Ox0.map (fun i => checkerSign (wordPos w i))).sum % 4 = 2 := by
    have hr := h.residue_sum_x_mod_four ha_ne (r := 0) (by omega)
    rw [ha_abs] at hr
    exact hr
  have hrx1 : (Ox1.map (fun i => checkerSign (wordPos w i))).sum % 4 = 2 := by
    have hr := h.residue_sum_x_mod_four ha_ne (r := 1) (by omega)
    rw [ha_abs] at hr
    exact hr
  have hry0 : (Oy0.map (fun i => checkerSign (wordPos w i))).sum % 4 = 2 := by
    have hr := h.residue_sum_y_mod_four hb_ne (r := 0) (by omega)
    rw [hb_abs] at hr
    exact hr
  have hge0 : 2 ≤ Ox0.length := by
    have := (unitSign_list_mod_four_eq_two
      (by intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact checkerSign_eq_one_or_neg_one _)
      hrx0).1
    simpa only [List.length_map] using this
  have hge1 : 2 ≤ Ox1.length := by
    have := (unitSign_list_mod_four_eq_two
      (by intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact checkerSign_eq_one_or_neg_one _)
      hrx1).1
    simpa only [List.length_map] using this
  have hsplit : Ox0.length + Ox1.length = O.length := by
    have hnot : Ox1 = O.filter (fun i => !decide ((wordPos w i).1 % 2 = 0)) := by
      apply List.filter_congr
      intro i _
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    rw [hnot]
    exact filter_length_add_not (fun i => decide ((wordPos w i).1 % 2 = 0)) O
  have hlenO : O.length = 4 := hg
  have hlen0 : Ox0.length = 2 := by omega
  have hlen1 : Ox1.length = 2 := by omega
  have hpair0 := unitSign_list_length_two_of_mod_four_eq_two
    (xs := Ox0.map (fun i => checkerSign (wordPos w i)))
    (by intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact checkerSign_eq_one_or_neg_one _)
    hrx0 (by simp [hlen0])
  have hpair1 := unitSign_list_length_two_of_mod_four_eq_two
    (xs := Ox1.map (fun i => checkerSign (wordPos w i)))
    (by intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact checkerSign_eq_one_or_neg_one _)
    hrx1 (by simp [hlen1])
  refine ⟨?_, hlen0, hlen1⟩
  have hmem_split : ∀ i ∈ O, i ∈ Ox0 ∨ i ∈ Ox1 := by
    intro i hi
    by_cases hx : (wordPos w i).1 % 2 = 0
    · exact Or.inl (List.mem_filter.mpr ⟨hi, decide_eq_true hx⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨hi, decide_eq_true (by omega)⟩)
  -- Express `Oy0`'s signed sum via the two `x`-lanes to eliminate mixed signs.
  have hoy0_sum :
      (Oy0.map (fun i => checkerSign (wordPos w i))).sum =
        ((Ox0.filter (fun i => decide ((wordPos w i).2 % 2 = 0))).map
          (fun i => checkerSign (wordPos w i))).sum +
        ((Ox1.filter (fun i => decide ((wordPos w i).2 % 2 = 0))).map
          (fun i => checkerSign (wordPos w i))).sum := by
    have hperm : Oy0.Perm
        (Ox0.filter (fun i => decide ((wordPos w i).2 % 2 = 0)) ++
         Ox1.filter (fun i => decide ((wordPos w i).2 % 2 = 0))) := by
      have hnd_app :
          (Ox0.filter (fun i => decide ((wordPos w i).2 % 2 = 0)) ++
           Ox1.filter (fun i => decide ((wordPos w i).2 % 2 = 0))).Nodup := by
        rw [List.nodup_append]
        refine ⟨((oddClassReps_nodup P w).filter _).filter _,
          ((oddClassReps_nodup P w).filter _).filter _, ?_⟩
        intro a ha b hb hab
        subst hab
        have h0 : (wordPos w a).1 % 2 = 0 :=
          of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2
        have h1 : (wordPos w a).1 % 2 = 1 :=
          of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp hb).1).2
        omega
      apply (List.perm_ext_iff_of_nodup ((oddClassReps_nodup P w).filter _) hnd_app).mpr
      intro i
      simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, Ox0, Ox1]
      constructor
      · rintro ⟨hiO, hiy⟩
        by_cases hx : (wordPos w i).1 % 2 = 0
        · exact Or.inl ⟨⟨hiO, hx⟩, hiy⟩
        · exact Or.inr ⟨⟨hiO, by omega⟩, hiy⟩
      · rintro (⟨⟨hiO, _⟩, hiy⟩ | ⟨⟨hiO, _⟩, hiy⟩) <;> exact ⟨hiO, hiy⟩
    rw [int_sum_perm (hperm.map _), List.map_append, int_sum_append]
  rcases hpair0 with h0p | h0n <;> rcases hpair1 with h1p | h1n
  · left
    intro i hi
    rcases hmem_split i hi with h0 | h1
    · exact forall_checkerSign_of_map_eq_pair (wordPos w) h0p i h0
    · exact forall_checkerSign_of_map_eq_pair (wordPos w) h1p i h1
  · exfalso
    have hall0 : ∀ i ∈ Ox0, (wordPos w i).2 % 2 = 0 := by
      intro i hi
      have hc := forall_checkerSign_of_map_eq_pair (wordPos w) h0p i hi
      have hx : (wordPos w i).1 % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hi).2
      unfold checkerSign at hc
      split at hc <;> omega
    have hall1 : ∀ i ∈ Ox1, (wordPos w i).2 % 2 = 0 := by
      intro i hi
      have hc := forall_checkerSign_of_map_eq_pair (wordPos w) h1n i hi
      have hx : (wordPos w i).1 % 2 = 1 := of_decide_eq_true (List.mem_filter.mp hi).2
      unfold checkerSign at hc
      split at hc <;> omega
    have hf0 : Ox0.filter (fun i => decide ((wordPos w i).2 % 2 = 0)) = Ox0 :=
      List.filter_eq_self.mpr (fun i hi => decide_eq_true (hall0 i hi))
    have hf1 : Ox1.filter (fun i => decide ((wordPos w i).2 % 2 = 0)) = Ox1 :=
      List.filter_eq_self.mpr (fun i hi => decide_eq_true (hall1 i hi))
    rw [hf0, hf1, h0p, h1n] at hoy0_sum
    simp at hoy0_sum
    omega
  · exfalso
    have hnone0 : Ox0.filter (fun i => decide ((wordPos w i).2 % 2 = 0)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      obtain ⟨hi0, hiy⟩ := List.mem_filter.mp hi
      have hc := forall_checkerSign_of_map_eq_pair (wordPos w) h0n i hi0
      have hx : (wordPos w i).1 % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hi0).2
      have hy : (wordPos w i).2 % 2 = 0 := of_decide_eq_true hiy
      unfold checkerSign at hc
      split at hc <;> omega
    have hnone1 : Ox1.filter (fun i => decide ((wordPos w i).2 % 2 = 0)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      obtain ⟨hi1, hiy⟩ := List.mem_filter.mp hi
      have hc := forall_checkerSign_of_map_eq_pair (wordPos w) h1p i hi1
      have hx : (wordPos w i).1 % 2 = 1 := of_decide_eq_true (List.mem_filter.mp hi1).2
      have hy : (wordPos w i).2 % 2 = 0 := of_decide_eq_true hiy
      unfold checkerSign at hc
      split at hc <;> omega
    rw [hnone0, hnone1] at hoy0_sum
    simp at hoy0_sum
    omega
  · right
    intro i hi
    rcases hmem_split i hi with h0 | h1
    · exact forall_checkerSign_of_map_eq_pair (wordPos w) h0n i h0
    · exact forall_checkerSign_of_map_eq_pair (wordPos w) h1n i h1

theorem ConsistentWord.drift_two_negTwo_growth_four_structure {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hg : wordGrowth P w = 4) :
    ((∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = 1) ∨
      (∀ i ∈ oddClassReps P w, checkerSign (wordPos w i) = -1)) ∧
    ((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 0))).length = 2 ∧
    ((oddClassReps P w).filter (fun i => decide ((wordPos w i).1 % 2 = 1))).length = 2 :=
  h.twoCellDiagonal_growth_four_structure ⟨Or.inl (by simp [hd]), Or.inr (by simp [hd])⟩ hg

/-! ## 7. Kernel sanity check on the standard 104-step highway (`g = 12`) -/

theorem standard_word_leftCount : leftCount 104 certifiedColor = 46 := by
  decide

theorem standard_word_rightCount : rightCount 104 certifiedColor = 58 := by
  decide

theorem standard_word_growthInt : wordGrowthInt 104 certifiedColor = 12 := by
  decide

/-- The standard 104-step highway word (`drift = (-2, -2)`) has exact growth `g = 12`, checked
purely in the Lean kernel. -/
theorem standard_word_growth : wordGrowth 104 certifiedColor = 12 := by
  have h1 := standard_word_consistent.growth_eq_turn_balance
  rw [standard_word_growthInt] at h1
  omega

/-- Non-vacuity check: the standard 104-step highway satisfies all headline growth theorems. -/
theorem standard_word_growth_sanity :
    wordGrowth 104 certifiedColor = 12 ∧
    wordGrowthInt 104 certifiedColor = (wordGrowth 104 certifiedColor : Int) ∧
    wordGrowth 104 certifiedColor % 4 = 0 ∧
    0 < wordGrowth 104 certifiedColor ∧
    2 * max (wordDrift 104 certifiedColor).1.natAbs (wordDrift 104 certifiedColor).2.natAbs ≤
      wordGrowth 104 certifiedColor :=
  ⟨standard_word_growth,
   standard_word_consistent.growth_eq_turn_balance,
   standard_word_consistent.growth_mod_four,
   standard_word_consistent.growth_pos,
   standard_word_consistent.two_mul_driftInf_le_growth⟩

end LangtonsAnt
