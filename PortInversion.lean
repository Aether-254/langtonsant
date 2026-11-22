/-!
# Port inversion parity kernels (`PortInversion.lean`)

Pure finite list combinatorics with **no imports at all**, independent of Langton's ant
geometry.  This file supplies the list-level inversion machinery needed by blueprint
items **L14** (0-1 port word inversion parity) and **L16** (abstract block decomposition
of the successor permutation parity) of `research/growth-blueprint-2026-11-22.md`
(§3.3 and §4.1 risk 1), in a repository that has no Mathlib and hence no
permutation-sign library (`Equiv.Perm.sign`).

## 1. Inversions on `List Nat`

* `listInv xs` — the number of index pairs `a < b` with `xs[a] > xs[b]`, recursively
  `listInv (x :: xs) = (xs.filter (· < x)).length + listInv xs`;
* `crossInv xs ys` — the number of pairs `x ∈ xs`, `y ∈ ys` with `x > y`; it sees only
  the *multisets*, which is what makes block rearrangements tractable;
* `listInv_append` : `listInv (xs ++ ys) = listInv xs + listInv ys + crossInv xs ys`;
* `listInv_eq_zero_of_pairwise_le` : weakly increasing lists have no inversions;
* `listInv_swap_adjacent_lt` / `listInv_swap_adjacent_mod` : swapping two adjacent
  distinct entries changes `listInv` by exactly `±1`, hence flips its parity;
  `listInv_swap_general_mod` : the same inside an arbitrary prefix;
* `listInv_reverse_of_pairwise_lt` : a reversed strictly increasing list of length `n`
  has `pairCount n = n (n-1) / 2` inversions, with `listInv_reverse_range'_one` the
  instance for `[1, 2, …, n]` (`pairCount`, `pairCount_eq_div`).

## 2. Adjacent transpositions — the replacement for `Equiv.Perm.sign`

* `AdjSwap xs ys` : one adjacent transposition of distinct entries;
* `SwapsTo k xs ys` : exactly `k` of them; `swapsTo_perm`, `swapsTo_nodup`;
* `swapsTo_parity` : `(listInv xs + listInv ys) % 2 = k % 2`, i.e. `k` adjacent
  transpositions of distinct entries flip the inversion parity exactly `k` times;
* cyclic shift: `listInv_range'_append_zero` : `listInv [1, 2, …, n, 0] = n`, hence
  `cycle_rotation_parity_odd` : one rotation of an even cycle of length `P = 2(M+1)`
  has odd parity `P - 1`.  This is the `1` of the blueprint's `1 + E + Σ …` shape.

## 3. Blueprint item L14 (0-1 port word)

* `countTrue`, `countFalse`, `wordInv` (`#{(a<b) : α[a] = true, α[b] = false}`),
  `rankSum` (sum of the `true` indices);
* `portWord_identity` (exact, no subtraction, no division):
  `wordInv α + rankSum α = A * B + pairCount A`, where `A = countTrue α`,
  `B = countFalse α` and `pairCount A = A (A-1) / 2`;
* `portWord_parity`, `portWord_parity_div` : the blueprint's
  `wordInv α + A (n-1) + rankSum α + A (A-1) / 2 ≡ 0 (mod 2)`, `n = α.length`.

## 4. Blueprint item L16 (abstract block decomposition)

* `stablePart k xs` : within-block stable reordering, `false` key first;
* `stablePart_parity` : for a `Nodup` block, `listInv (stablePart k b)` differs from
  `listInv b` in parity by exactly `wordInv (b.map k)` — the within-block term
  `Σ_v invCount β_v`;
* `pairCross blk` and `listInv_flatten` :
  `listInv blk.flatten = Σ listInv (block) + pairCross blk`;
* `crossInv_stablePart_left/right`, `pairCross_map_stablePart` : the cross-block term is
  blind to reorderings *inside* the blocks;
* `pairCross_swap_adjacent_parity` : swapping two adjacent blocks changes the cross-block
  parity by `crossInv a b + crossInv b a` (the block-permutation term `E`);
* `block_decomposition` : the composite parity is the sum of the two within-block terms
  and `E = pairCross ord + pairCross nodes`;
* `block_decomposition_blueprint` : the blueprint's own `1 + E + Σ_v(α_v + β_v) ≡ 0`
  shape, once the composite reordering has single-even-cycle parity.

## Conventions and sanity checks

* The blueprint's L14 parity formula is **correct as stated**; `portWord_identity` is the
  sharper integer identity, and `mul_length_pred` records why `A (n-1)` and
  `A B + A (A-1)` agree modulo 2 (they differ by the even number `A (A-1)`), so both
  arithmetisations may be used.
* In L16 the `α` key word of a block is read *after* the within-block `β` sorting, i.e.
  the last stage is the inverse of the `α` sort of the `β`-sorted block; the phase list
  `nodes.flatten` is the source and the block order of `ord` is the target, so
  `listInv target + listInv source ≡ 1` is what turns `block_decomposition` into
  `block_decomposition_blueprint`.
* Every numeric identity was brute-force checked with temporary `#eval`s before being
  proved (checks, all of which passed, then deleted):
  `listInv` against a pairwise index reference on all lists of length ≤ 6 over `{0,1,2}`
  and on all permutations of `range n` for `n ≤ 6`; sorted lists have `listInv = 0`;
  adjacent swaps flip the parity; `listInv (range' 1 n ++ [0]) = n` and
  `listInv (range' 1 n).reverse = n(n-1)/2` for `n ≤ 8`; the reversed-increasing formula on
  all subsets of `range 7`; `countTrue`/`countFalse`/`wordInv`/`rankSum` against references
  and the L14 identity/parity on all Boolean words of length ≤ 7; `stablePart_parity` and
  the filter/cross lemmas on all permutations of `range n` (`n ≤ 6`) and all lists of
  length ≤ 6 over `{0,1,2}` with five different keys; `listInv_flatten`,
  `pairCross_map_stablePart`, `pairCross_swap_adjacent_parity` and both block theorems on
  block lists cut from permutations of `range n` (`n ≤ 5`) with block widths `1,2,3`, every
  block-order permutation and all key pairs.
* Every declaration is checked by the Lean kernel: no `sorry`, no `axiom`, no
  `native_decide`.  `#print axioms` on the main theorems reports only `propext`,
  `Quot.sound` and (for two results using `List.filter_eq_nil_iff`) `Classical.choice`.
-/

namespace PortInversion

/-! ## 1. Inversion counts on `List Nat` -/

/-- `listInv xs` is the number of index pairs `a < b` with `xs[a] > xs[b]`.

Recursive form: the new head `x` contributes exactly the elements of the tail
that are strictly smaller than it. -/
def listInv : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.filter (fun y => y < x)).length + listInv xs

/-- `crossInv xs ys` counts the pairs `(x, y) ∈ xs × ys` with `x > y`.
It only sees the *multisets* of `xs` and `ys`, not their orders; that is what
makes it the correct bookkeeping device for block rearrangements. -/
def crossInv : List Nat → List Nat → Nat
  | [], _ => 0
  | x :: xs, ys => (ys.filter (fun y => y < x)).length + crossInv xs ys

@[simp] theorem listInv_nil : listInv [] = 0 := rfl

@[simp] theorem listInv_cons (x : Nat) (xs : List Nat) :
    listInv (x :: xs) = (xs.filter (fun y => y < x)).length + listInv xs := rfl

@[simp] theorem crossInv_nil_left (ys : List Nat) : crossInv [] ys = 0 := rfl

@[simp] theorem crossInv_cons (x : Nat) (xs ys : List Nat) :
    crossInv (x :: xs) ys = (ys.filter (fun y => y < x)).length + crossInv xs ys := rfl

@[simp] theorem crossInv_nil_right (xs : List Nat) : crossInv xs [] = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [crossInv_cons, ih, Nat.add_zero]; rfl

/-- `crossInv [x] ys` is the number of elements of `ys` below `x`. -/
theorem crossInv_singleton_left (x : Nat) (ys : List Nat) :
    crossInv [x] ys = (ys.filter (fun y => y < x)).length := by
  rw [crossInv_cons, crossInv_nil_left, Nat.add_zero]

/-- `crossInv xs [x]` is the number of elements of `xs` above `x`. -/
theorem crossInv_singleton_right (x : Nat) : ∀ xs : List Nat,
    crossInv xs [x] = (xs.filter (fun u => x < u)).length
  | [] => rfl
  | u :: us => by
      rw [crossInv_cons, crossInv_singleton_right x us]
      by_cases h : x < u <;> simp [h] <;> omega

theorem crossInv_append_left (as bs cs : List Nat) :
    crossInv (as ++ bs) cs = crossInv as cs + crossInv bs cs := by
  induction as with
  | nil => rw [List.nil_append, crossInv_nil_left, Nat.zero_add]
  | cons x as ih =>
      rw [List.cons_append, crossInv_cons, ih, crossInv_cons]
      omega

theorem crossInv_append_right (as bs cs : List Nat) :
    crossInv as (bs ++ cs) = crossInv as bs + crossInv as cs := by
  induction as with
  | nil => rfl
  | cons x as ih =>
      have h1 : (bs ++ cs).filter (fun y => y < x)
          = (bs.filter (fun y => y < x)) ++ (cs.filter (fun y => y < x)) :=
        List.filter_append ..
      rw [crossInv_cons, h1, List.length_append, crossInv_cons, crossInv_cons, ih]
      omega

/-- Peeling one element off the right argument of `crossInv`. -/
theorem crossInv_cons_right (as : List Nat) (x : Nat) (bs : List Nat) :
    crossInv as (x :: bs) = crossInv as [x] + crossInv as bs := by
  rw [show x :: bs = [x] ++ bs from rfl, crossInv_append_right]

/-- Splitting a list into a prefix and a suffix: within-part inversions plus the
cross pairs. -/
theorem listInv_append (as bs : List Nat) :
    listInv (as ++ bs) = listInv as + listInv bs + crossInv as bs := by
  induction as with
  | nil => rw [List.nil_append, listInv_nil, crossInv_nil_left]; omega
  | cons x as ih =>
      have h1 : ((as ++ bs).filter (fun y => y < x)).length
          = (as.filter (fun y => y < x)).length + (bs.filter (fun y => y < x)).length := by
        rw [List.filter_append, List.length_append]
      rw [List.cons_append, listInv_cons, h1, ih, crossInv_cons, listInv_cons]
      omega

theorem listInv_singleton (x : Nat) : listInv [x] = 0 := rfl

/-- A weakly increasing list has no inversions. -/
theorem listInv_eq_zero_of_pairwise_le : ∀ (xs : List Nat), xs.Pairwise (· ≤ ·) → listInv xs = 0
  | [], _ => rfl
  | x :: xs, h => by
      cases h with
      | cons hx hxs =>
          have hnil : (xs.filter (fun y => y < x)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro a ha
            have hxa : x ≤ a := hx a ha
            simp
            omega
          rw [listInv_cons, hnil, List.length_nil, Nat.zero_add,
            listInv_eq_zero_of_pairwise_le xs hxs]

/-! ### Number-theoretic triangular count

`pairCount n` is `n * (n - 1) / 2` (see `pairCount_eq_div`), kept in recursive
form so that the L14 induction below never needs division. -/

/-- `pairCount n = n * (n - 1) / 2`, recursively: `0, 0, 1, 3, 6, 10, …`. -/
def pairCount : Nat → Nat
  | 0 => 0
  | n + 1 => pairCount n + n

theorem pairCount_zero : pairCount 0 = 0 := rfl

theorem pairCount_succ (n : Nat) : pairCount (n + 1) = pairCount n + n := rfl

theorem two_mul_pairCount (n : Nat) : 2 * pairCount n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show 2 * (pairCount n + n) = (n + 1) * (n + 1 - 1)
      rw [Nat.mul_add, ih, Nat.add_sub_cancel]
      cases n with
      | zero => rfl
      | succ m =>
          show (m + 1) * m + 2 * (m + 1) = (m + 1 + 1) * (m + 1)
          rw [Nat.mul_comm (m + 1 + 1) (m + 1), Nat.mul_succ (m + 1) (m + 1),
            Nat.mul_succ (m + 1) m, Nat.two_mul]
          omega

/-- The closed form of `pairCount`. -/
theorem pairCount_eq_div (n : Nat) : pairCount n = n * (n - 1) / 2 := by
  rw [← two_mul_pairCount n, Nat.mul_comm 2 (pairCount n), Nat.mul_div_left _ (by decide)]


/-! ## 2. Adjacent transpositions and permutation parity -/

/-- Swapping two adjacent *increasing* entries increases the inversion count by one. -/
theorem listInv_swap_adjacent_lt {a b : Nat} (hab : a < b) (rest : List Nat) :
    listInv (b :: a :: rest) = listInv (a :: b :: rest) + 1 := by
  have h1 : ((a :: rest).filter (fun y => y < b)).length
      = 1 + (rest.filter (fun y => y < b)).length := by
    rw [List.filter_cons_of_pos (p := fun y => y < b) (by simpa using hab)]
    simp
    omega
  have h2 : ((b :: rest).filter (fun y => y < a)).length
      = (rest.filter (fun y => y < a)).length := by
    rw [List.filter_cons_of_neg (p := fun y => y < a) (by simp; omega)]
  simp only [listInv_cons]
  rw [h1, h2]
  omega

/-- Swapping two adjacent distinct entries changes the inversion count by exactly one,
so the parity always flips. -/
theorem listInv_swap_adjacent_mod {a b : Nat} (hab : a ≠ b) (rest : List Nat) :
    (listInv (a :: b :: rest) + listInv (b :: a :: rest)) % 2 = 1 := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · have h1 := listInv_swap_adjacent_lt h rest
    omega
  · have h1 := listInv_swap_adjacent_lt h rest
    omega

/-- `crossInv` is blind to the order of two different head elements. -/
theorem crossInv_cons_cons (as : List Nat) (a b : Nat) (rest : List Nat) :
    crossInv as (a :: b :: rest) = crossInv as (b :: a :: rest) := by
  rw [show a :: b :: rest = [a] ++ [b] ++ rest from rfl,
    show b :: a :: rest = [b] ++ [a] ++ rest from rfl,
    crossInv_append_right, crossInv_append_right, crossInv_append_right, crossInv_append_right]
  omega

/-- The parity flip survives inside an arbitrary prefix, as long as the two swapped
entries are distinct. -/
theorem listInv_swap_general_mod {a b : Nat} (hab : a ≠ b) (pre rest : List Nat) :
    (listInv (pre ++ a :: b :: rest) + listInv (pre ++ b :: a :: rest)) % 2 = 1 := by
  have h1 : listInv (pre ++ a :: b :: rest)
      = listInv pre + listInv (a :: b :: rest) + crossInv pre (a :: b :: rest) :=
    listInv_append ..
  have h2 : listInv (pre ++ b :: a :: rest)
      = listInv pre + listInv (b :: a :: rest) + crossInv pre (a :: b :: rest) := by
    rw [listInv_append, crossInv_cons_cons]
  have hmod := listInv_swap_adjacent_mod hab rest
  rw [h1, h2]
  omega

/-- `AdjSwap xs ys`: `ys` is obtained from `xs` by swapping one pair of adjacent,
distinct entries. -/
def AdjSwap (xs ys : List Nat) : Prop :=
  ∃ (pre rest : List Nat) (a b : Nat),
    a ≠ b ∧ xs = pre ++ a :: b :: rest ∧ ys = pre ++ b :: a :: rest

theorem adjSwap_parity {xs ys : List Nat} (h : AdjSwap xs ys) :
    (listInv xs + listInv ys) % 2 = 1 := by
  obtain ⟨pre, rest, a, b, hab, rfl, rfl⟩ := h
  exact listInv_swap_general_mod hab pre rest

theorem adjSwap_perm {xs ys : List Nat} (h : AdjSwap xs ys) : xs.Perm ys := by
  obtain ⟨pre, rest, a, b, hab, rfl, rfl⟩ := h
  have htail : (b :: a :: rest).Perm (a :: b :: rest) := List.Perm.swap a b rest
  exact (List.Perm.append (List.Perm.refl pre) htail).symm

/-- `SwapsTo k xs ys`: `ys` is obtained from `xs` by exactly `k` adjacent transpositions
of distinct entries (all intermediate lists of the chain being distinct-valued where needed). -/
inductive SwapsTo : Nat → List Nat → List Nat → Prop
  | refl (xs : List Nat) : SwapsTo 0 xs xs
  | step {k : Nat} {xs ys zs : List Nat} :
      SwapsTo k xs ys → AdjSwap ys zs → SwapsTo (k + 1) xs zs

theorem swapsTo_perm {k : Nat} {xs ys : List Nat} (h : SwapsTo k xs ys) : xs.Perm ys := by
  induction h with
  | refl xs => exact List.Perm.refl xs
  | step _ hadj ih => exact ih.trans (adjSwap_perm hadj)

theorem swapsTo_nodup {k : Nat} {xs ys : List Nat} (h : SwapsTo k xs ys) (hn : xs.Nodup) :
    ys.Nodup := (swapsTo_perm h).nodup hn

/-- **Permutation parity, list form (blueprint §4.1 risk 1).**
`k` adjacent transpositions of distinct entries flip the inversion parity exactly `k` times. -/
theorem swapsTo_parity : ∀ {k : Nat} {xs ys : List Nat},
    SwapsTo k xs ys → (listInv xs + listInv ys) % 2 = k % 2
  | 0, xs, ys, h => by
      cases h with
      | refl => omega
  | k + 1, xs, ys, h => by
      cases h with
      | step hk hadj =>
          have ih := swapsTo_parity hk
          have ha := adjSwap_parity hadj
          omega

/-! ## 3. The 0–1 port word: blueprint item L14 -/

/-- Number of `true` entries of a Boolean list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | true :: l => countTrue l + 1
  | false :: l => countTrue l

/-- Number of `false` entries of a Boolean list. -/
def countFalse : List Bool → Nat
  | [] => 0
  | true :: l => countFalse l
  | false :: l => countFalse l + 1

theorem countTrue_add_countFalse : ∀ α : List Bool, countTrue α + countFalse α = α.length
  | [] => rfl
  | true :: l => by
      show countTrue l + 1 + countFalse l = (l.length + 1)
      have ih := countTrue_add_countFalse l
      omega
  | false :: l => by
      show countTrue l + (countFalse l + 1) = (l.length + 1)
      have ih := countTrue_add_countFalse l
      omega

theorem countTrue_map (k : Nat → Bool) : ∀ l : List Nat,
    countTrue (l.map k) = (l.filter k).length
  | [] => rfl
  | x :: xs => by
      have ih := countTrue_map k xs
      cases h : k x with
      | false =>
          rw [List.map_cons, h, List.filter_cons_of_neg (by rw [h]; exact Bool.false_ne_true)]
          show countTrue (List.map k xs) = (List.filter k xs).length
          exact ih
      | true =>
          rw [List.map_cons, h, List.filter_cons_of_pos (by rw [h])]
          show countTrue (List.map k xs) + 1 = (List.filter k xs).length + 1
          rw [ih]

theorem countFalse_map (k : Nat → Bool) : ∀ l : List Nat,
    countFalse (l.map k) = (l.filter (fun x => !k x)).length
  | [] => rfl
  | x :: xs => by
      have ih := countFalse_map k xs
      cases h : k x with
      | false =>
          rw [List.map_cons, h, List.filter_cons_of_pos (by rw [h]; rfl)]
          show countFalse (List.map k xs) + 1 = (List.filter (fun x => !k x) xs).length + 1
          rw [ih]
      | true =>
          rw [List.map_cons, h, List.filter_cons_of_neg (by rw [h]; exact Bool.false_ne_true)]
          show countFalse (List.map k xs) = (List.filter (fun x => !k x) xs).length
          exact ih

/-- `wordInv α` counts the pairs `a < b` with `α[a] = true` and `α[b] = false`
(the L14 "port word" inversion count). -/
def wordInv : List Bool → Nat
  | [] => 0
  | true :: l => countFalse l + wordInv l
  | false :: l => wordInv l

/-- `rankSum α` is the sum of the indices of the `true` entries (L14 `rankSum`). -/
def rankSum : List Bool → Nat
  | [] => 0
  | _ :: l => rankSum l + countTrue l

theorem rankSum_zero : rankSum [] = 0 := rfl

/-- **L14, exact integer form.**  `wordInv α + rankSum α` equals the number of
`true`–`false` pairs plus the number of `true`–`true` pairs. -/
theorem portWord_identity : ∀ α : List Bool,
    wordInv α + rankSum α = countTrue α * countFalse α + pairCount (countTrue α)
  | [] => rfl
  | true :: l => by
      have ih := portWord_identity l
      show countFalse l + wordInv l + (rankSum l + countTrue l)
        = (countTrue l + 1) * countFalse l + pairCount (countTrue l + 1)
      rw [Nat.succ_mul]
      show countFalse l + wordInv l + (rankSum l + countTrue l)
        = (countTrue l * countFalse l + countFalse l) + (pairCount (countTrue l) + countTrue l)
      omega
  | false :: l => by
      have ih := portWord_identity l
      show wordInv l + (rankSum l + countTrue l)
        = countTrue l * (countFalse l + 1) + pairCount (countTrue l)
      rw [Nat.mul_succ]
      omega

/-- `countTrue α * (α.length - 1)` and `countTrue α * countFalse α + 2 * pairCount _`
agree, i.e. the two possible arithmetisations of the L14 linear term. -/
theorem mul_length_pred (α : List Bool) :
    countTrue α * (α.length - 1) = countTrue α * countFalse α + 2 * pairCount (countTrue α) := by
  have hlen : α.length = countTrue α + countFalse α := (countTrue_add_countFalse α).symm
  rw [hlen, two_mul_pairCount]
  cases hA : countTrue α with
  | zero => simp
  | succ a =>
      have h1 : a + 1 + countFalse α - 1 = a + countFalse α := by omega
      have h2 : a + 1 - 1 = a := by omega
      rw [h1, h2, Nat.mul_add]
      omega

/-- **L14 parity identity (blueprint form).**  For every Boolean word `α`,
`wordInv α + A (n-1) + rankSum α + A (A-1) / 2` is even, where `A = countTrue α`
and `n = α.length`.  Here `A (A-1) / 2` is kept as the division-free `pairCount A`. -/
theorem portWord_parity (α : List Bool) :
    (wordInv α + countTrue α * (α.length - 1) + rankSum α + pairCount (countTrue α)) % 2 = 0 := by
  have hid := portWord_identity α
  have hmul := mul_length_pred α
  omega

/-- **L14 parity identity, literally in the blueprint's shape** (`A (A-1) / 2` written
with division). -/
theorem portWord_parity_div (α : List Bool) :
    (wordInv α + countTrue α * (α.length - 1) + rankSum α
      + countTrue α * (countTrue α - 1) / 2) % 2 = 0 := by
  rw [← pairCount_eq_div (countTrue α)]
  exact portWord_parity α

theorem range'_one_pos (n : Nat) {x : Nat} (hx : x ∈ List.range' 1 n) : 0 < x := by
  rw [List.mem_range'] at hx
  obtain ⟨i, _, rfl⟩ := hx
  omega

theorem range'_one_le (n : Nat) {x : Nat} (hx : x ∈ List.range' 1 n) : x ≤ n := by
  rw [List.mem_range'] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  omega

/-- **Reversed strictly increasing list.**  Reversing a strictly increasing list of
length `n` produces the maximal inversion count `n (n-1) / 2` (`pairCount n`). -/
theorem listInv_reverse_of_pairwise_lt : ∀ xs : List Nat, xs.Pairwise (· < ·) →
    listInv xs.reverse = pairCount xs.length
  | [], _ => rfl
  | x :: ys, h => by
      cases h with
      | cons hx hys =>
          rw [List.reverse_cons, listInv_append, listInv_singleton, crossInv_singleton_right]
          have hof : ys.reverse.filter (fun y => x < y) = ys.reverse := by
            rw [List.filter_eq_self]
            intro a ha
            exact decide_eq_true (hx a (List.mem_reverse.mp ha))
          rw [hof, List.length_reverse, listInv_reverse_of_pairwise_lt ys hys, List.length_cons,
            pairCount_succ]
          omega

theorem range'_one_pairwise_lt : ∀ n : Nat, (List.range' 1 n).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | n + 1 => by
      rw [List.range'_concat, List.pairwise_append]
      refine ⟨range'_one_pairwise_lt n, ?_, ?_⟩
      · exact List.Pairwise.cons (fun a' ha' => by simp at ha') List.Pairwise.nil
      · intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        have h1 := range'_one_le n ha
        omega

/-- Reversed `[1, 2, …, n]`, i.e. a strictly increasing list of length `n` reversed,
has exactly `n (n-1) / 2` inversions. -/
theorem listInv_reverse_range'_one (n : Nat) :
    listInv (List.range' 1 n).reverse = n * (n - 1) / 2 := by
  rw [listInv_reverse_of_pairwise_lt _ (range'_one_pairwise_lt n), List.length_range',
    pairCount_eq_div]

/-! ### The cyclic shift of `range n` (parity of the single `succ P` cycle) -/

theorem listInv_range'_one : ∀ n : Nat, listInv (List.range' 1 n) = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.range'_concat, Nat.one_mul, listInv_append, crossInv_singleton_right,
        listInv_range'_one n]
      have hnil : (List.range' 1 n).filter (fun u => 1 + n < u) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := range'_one_le n ha
        simp
        omega
      rw [hnil]
      rfl

/-- One cyclic rotation of `range (n+1)`, namely `[1, 2, …, n, 0]`, has exactly `n`
inversions.  (A single cycle of even length `P = 2M+2` hence has odd parity `P - 1`.) -/
theorem listInv_range'_append_zero : ∀ n : Nat, listInv (List.range' 1 n ++ [0]) = n
  | 0 => rfl
  | n + 1 => by
      rw [List.range'_concat, Nat.one_mul, listInv_append, listInv_append,
        crossInv_append_left, crossInv_singleton_right, crossInv_singleton_right,
        crossInv_singleton_right, listInv_range'_one]
      have hpos : (List.range' 1 n).filter (fun u => 0 < u) = List.range' 1 n := by
        rw [List.filter_eq_self]
        intro a ha
        simpa using range'_one_pos n ha
      have hnil : (List.range' 1 n).filter (fun u => 1 + n < u) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := range'_one_le n ha
        simp
        omega
      have hone : ([1 + n].filter (fun u => 0 < u)).length = 1 := by
        rw [List.filter_cons_of_pos (by simp; omega)]
        rfl
      rw [hnil, hpos, List.length_range', hone]
      show 0 + 0 + 0 + 0 + (n + 1) = n + 1
      omega

/-- The rotation parity of a single cycle of even length `2M + 2` is odd. -/
theorem cycle_rotation_parity_odd (M : Nat) :
    listInv ((List.range' 1 (2 * M + 1)) ++ [0]) % 2 = 1 := by
  rw [listInv_range'_append_zero]
  omega

/-! ## 4. Blueprint item L16: abstract block decomposition -/

/-- Stable reordering of a list by a Boolean key: first all entries whose key is
`false`, then all entries whose key is `true`, each part keeping its relative order. -/
def stablePart (k : Nat → Bool) (xs : List Nat) : List Nat :=
  xs.filter (fun x => !k x) ++ xs.filter (fun x => k x)

theorem stablePart_nil (k : Nat → Bool) : stablePart k [] = [] := rfl

/-- Splitting a filter into the two halves of a Boolean key. -/
theorem filter_split_count (p k : Nat → Bool) : ∀ l : List Nat,
    (l.filter (fun x => p x && !k x)).length + (l.filter (fun x => p x && k x)).length
      = (l.filter p).length
  | [] => rfl
  | x :: xs => by
      have ih := filter_split_count p k xs
      cases hp : p x <;> cases hk : k x <;> simp [hp, hk] at ih ⊢ <;> omega

/-- Filtering a stable partition by any predicate does not change the count. -/
theorem filter_stablePart_count (p k : Nat → Bool) (l : List Nat) :
    ((stablePart k l).filter p).length = (l.filter p).length := by
  rw [stablePart, List.filter_append, List.length_append, List.filter_filter, List.filter_filter]
  exact filter_split_count p k l

/-- If `x` is not in `l`, then every element of `l` is either below or above `x`,
so the two strict filters exhaust `l`. -/
theorem filter_lt_add_filter_gt (x : Nat) : ∀ l : List Nat, x ∉ l →
    (l.filter (fun y => y < x)).length + (l.filter (fun u => x < u)).length = l.length
  | [], _ => rfl
  | y :: ys, h => by
      have hy : y ≠ x := by
        intro he
        exact h (he ▸ List.mem_cons_self)
      have hys : x ∉ ys := fun hm => h (List.mem_cons_of_mem y hm)
      have ih := filter_lt_add_filter_gt x ys hys
      by_cases hyx : y < x
      · have hxy : ¬ (x < y) := by omega
        rw [List.filter_cons_of_pos (p := fun z => z < x) (by simp [hyx]),
          List.filter_cons_of_neg (p := fun z => x < z) (by simp [hxy])]
        simp only [List.length_cons]
        omega
      · have hxy : x < y := by omega
        rw [List.filter_cons_of_neg (p := fun z => z < x) (by simp [hyx]),
          List.filter_cons_of_pos (p := fun z => x < z) (by simp [hxy])]
        simp only [List.length_cons]
        omega

/-- A stable partition changes the inversion count parity by exactly the inversion
count of the key word.  This is the L16 *within-block* stage. -/
theorem stablePart_parity (k : Nat → Bool) : ∀ l : List Nat, l.Nodup →
    (listInv (stablePart k l) + wordInv (l.map k)) % 2 = listInv l % 2
  | [], _ => rfl
  | x :: xs, hnodup => by
      have hx : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have ih := stablePart_parity k xs hxs
      have hxf : x ∉ xs.filter (fun y => !k y) := fun hm =>
        hx (List.Sublist.subset (List.filter_sublist (p := fun y => !k y) (l := xs)) hm)
      cases hk : k x with
      | false =>
          have hsp : stablePart k (x :: xs) = x :: stablePart k xs := by
            rw [stablePart, List.filter_cons_of_pos (p := fun y => !k y) (by rw [hk]; rfl),
              List.filter_cons_of_neg (p := fun y => k y) (by rw [hk]; exact Bool.false_ne_true),
              stablePart, List.cons_append]
          have hcnt : ((stablePart k xs).filter (fun y => y < x)).length
              = (xs.filter (fun y => y < x)).length := filter_stablePart_count _ k xs
          rw [hsp, listInv_cons, List.map_cons, hk, wordInv, listInv_cons, hcnt]
          omega
      | true =>
          have hsp : stablePart k (x :: xs)
              = xs.filter (fun y => !k y) ++ x :: xs.filter (fun y => k y) := by
            rw [stablePart, List.filter_cons_of_neg (p := fun y => !k y) (by rw [hk]; exact Bool.false_ne_true),
              List.filter_cons_of_pos (p := fun y => k y) (by rw [hk])]
          have hsp' : stablePart k xs = xs.filter (fun y => !k y) ++ xs.filter (fun y => k y) := rfl
          rw [hsp', listInv_append] at ih
          have hcf : countFalse (xs.map k) = (xs.filter (fun y => !k y)).length := countFalse_map k xs
          have hsplit : ((xs.filter (fun y => !k y)).filter (fun y => y < x)).length
              + ((xs.filter (fun y => k y)).filter (fun y => y < x)).length
              = (xs.filter (fun y => y < x)).length := by
            rw [List.filter_filter, List.filter_filter]
            exact filter_split_count (fun y => y < x) k xs
          have htri := filter_lt_add_filter_gt x (xs.filter (fun y => !k y)) hxf
          rw [hsp, List.map_cons, hk, wordInv, listInv_cons, listInv_append, listInv_cons,
            crossInv_cons_right, crossInv_singleton_right,
            hcf]
          omega

/-- `crossInv` of a filtered list splits according to the Boolean key. -/
theorem crossInv_filter_split (k : Nat → Bool) (b : List Nat) : ∀ a : List Nat,
    crossInv a b = crossInv (a.filter (fun x => !k x)) b + crossInv (a.filter (fun x => k x)) b
  | [] => rfl
  | x :: xs => by
      have ih := crossInv_filter_split k b xs
      cases hk : k x with
      | false =>
          have h1f : (x :: xs).filter (fun y => !k y) = x :: xs.filter (fun y => !k y) := by
            rw [List.filter_cons_of_pos (p := fun y => !k y) (by rw [hk]; rfl)]
          have h2f : (x :: xs).filter (fun y => k y) = xs.filter (fun y => k y) := by
            rw [List.filter_cons_of_neg (p := fun y => k y) (by rw [hk]; exact Bool.false_ne_true)]
          rw [crossInv_cons, h1f, h2f, crossInv_cons, ih]
          omega
      | true =>
          have h1t : (x :: xs).filter (fun y => !k y) = xs.filter (fun y => !k y) := by
            rw [List.filter_cons_of_neg (p := fun y => !k y) (by rw [hk]; exact Bool.false_ne_true)]
          have h2t : (x :: xs).filter (fun y => k y) = x :: xs.filter (fun y => k y) := by
            rw [List.filter_cons_of_pos (p := fun y => k y) (by rw [hk])]
          rw [crossInv_cons, h1t, h2t, crossInv_cons, ih]
          omega

/-- Stable reordering leaves `crossInv` of the *first* argument unchanged. -/
theorem crossInv_stablePart_left (k : Nat → Bool) (b a : List Nat) :
    crossInv (stablePart k a) b = crossInv a b := by
  have h := crossInv_filter_split k b a
  rw [stablePart, crossInv_append_left, ← h]

/-- Stable reordering leaves `crossInv` of the *second* argument unchanged. -/
theorem crossInv_stablePart_right (k : Nat → Bool) (a b : List Nat) :
    crossInv a (stablePart k b) = crossInv a b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      rw [crossInv_cons, crossInv_cons, filter_stablePart_count (fun y => y < x) k b, ih]

/-- Inserting an element into a list, at any position, is a permutation. -/
theorem perm_append_singleton_insert (x : Nat) : ∀ (f t : List Nat),
    (f ++ x :: t).Perm (x :: (f ++ t))
  | [], _ => List.Perm.refl _
  | y :: f, t => by
      have ih := perm_append_singleton_insert x f t
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y (f ++ t))

/-- A Boolean split of a list permutes it. -/
theorem filter_not_append_filter_perm (k : Nat → Bool) : ∀ l : List Nat,
    ((l.filter (fun x => !k x)) ++ (l.filter k)).Perm l
  | [] => List.Perm.nil
  | x :: xs => by
      have ih := filter_not_append_filter_perm k xs
      cases hk : k x with
      | false =>
          have h1f : (x :: xs).filter (fun y => !k y) = x :: xs.filter (fun y => !k y) := by
            rw [List.filter_cons_of_pos (p := fun y => !k y) (by rw [hk]; rfl)]
          have h2f : (x :: xs).filter (fun y => k y) = xs.filter (fun y => k y) := by
            rw [List.filter_cons_of_neg (p := fun y => k y) (by rw [hk]; exact Bool.false_ne_true)]
          rw [h1f, h2f, List.cons_append]
          exact List.Perm.cons x ih
      | true =>
          have h1t : (x :: xs).filter (fun y => !k y) = xs.filter (fun y => !k y) := by
            rw [List.filter_cons_of_neg (p := fun y => !k y) (by rw [hk]; exact Bool.false_ne_true)]
          have h2t : (x :: xs).filter (fun y => k y) = x :: xs.filter (fun y => k y) := by
            rw [List.filter_cons_of_pos (p := fun y => k y) (by rw [hk])]
          rw [h1t, h2t]
          exact (perm_append_singleton_insert x _ _).trans (List.Perm.cons x ih)

/-- A stable partition is a permutation of the original list. -/
theorem stablePart_perm (k : Nat → Bool) (l : List Nat) : (stablePart k l).Perm l :=
  filter_not_append_filter_perm k l

theorem nodup_stablePart {k : Nat → Bool} {l : List Nat} (h : l.Nodup) :
    (stablePart k l).Nodup := (stablePart_perm k l).symm.nodup h

/-! ### Block decomposition -/

/-- Total cross-block inversion count of a block list (block pairs, first block earlier). -/
def pairCross : List (List Nat) → Nat
  | [] => 0
  | b :: bs => crossInv b bs.flatten + pairCross bs

/-- **Flatten decomposition.**  The inversion count of a flattened block list is the sum of
the within-block counts plus all cross-block pairs. -/
theorem listInv_flatten : ∀ blk : List (List Nat),
    listInv blk.flatten = (blk.map listInv).sum + pairCross blk
  | [] => rfl
  | b :: bs => by
      have ih := listInv_flatten bs
      rw [List.flatten_cons, listInv_append, ih]
      simp only [List.map_cons, List.sum_cons, pairCross]
      omega

/-- `crossInv` against a flattened stable-partitioned block list is unchanged. -/
theorem crossInv_flatten_map_stablePart (k : Nat → Bool) (a : List Nat) :
    ∀ bs : List (List Nat), crossInv a ((bs.map (stablePart k)).flatten) = crossInv a bs.flatten
  | [] => rfl
  | b :: bs => by
      have ih := crossInv_flatten_map_stablePart k a bs
      rw [List.map_cons, List.flatten_cons, crossInv_append_right, crossInv_stablePart_right, ih,
        List.flatten_cons, crossInv_append_right]

/-- Stable reordering *inside* the blocks does not change the cross-block term. -/
theorem pairCross_map_stablePart (k : Nat → Bool) : ∀ blk : List (List Nat),
    pairCross (blk.map (stablePart k)) = pairCross blk
  | [] => rfl
  | b :: bs => by
      have ih := pairCross_map_stablePart k bs
      rw [List.map_cons, pairCross, ih, pairCross, crossInv_stablePart_left,
        crossInv_flatten_map_stablePart]

/-- Swapping two adjacent blocks changes the cross-block parity by
`crossInv a b + crossInv b a` (this is the block-permutation term of L16). -/
theorem pairCross_swap_adjacent_parity (a b : List Nat) (r : List (List Nat)) :
    (pairCross (a :: b :: r) + pairCross (b :: a :: r)) % 2
      = (crossInv a b + crossInv b a) % 2 := by
  simp only [pairCross, List.flatten_cons, crossInv_append_right]
  omega

/-- Summing is invariant under permutation. -/
theorem perm_sum {l1 l2 : List Nat} (h : l1.Perm l2) : l1.sum = l2.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons]; rw [ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih2 ih3 => exact ih2.trans ih3

/-- Termwise parity matching bounds the parity of a sum of two block sums. -/
theorem sum_mod_two_congr (f g h : List Nat → Nat) : ∀ blk : List (List Nat),
    (∀ b ∈ blk, (f b + g b) % 2 = h b % 2) →
      ((blk.map f).sum + (blk.map g).sum) % 2 = (blk.map h).sum % 2
  | [], _ => rfl
  | b :: bs, hb => by
      have h0 := hb b List.mem_cons_self
      have hrest := sum_mod_two_congr f g h bs (fun c hc => hb c (List.mem_cons_of_mem b hc))
      simp only [List.map_cons, List.sum_cons] at hrest ⊢
      omega

/-- **L16, abstract block decomposition.**  Reorder the blocks of `nodes` into the block
order `ord` (a permutation of the block list), and stable-partition each block first by
`kB` and then by `kA`.  The parity of
`listInv target flatten + listInv source flatten` is the sum of

* the within-block `kB` key-word inversion counts over the source blocks,
* the within-block `kA` key-word inversion counts over the target blocks,
* the cross-block term `pairCross ord + pairCross nodes` of the block permutation.

Hence the blueprint's `1 + E + Sum_v (invCount a_v + invCount b_v) = 0` shape
(use `block_decomposition_blueprint` with the single-cycle parity of the successor map,
cf. `cycle_rotation_parity_odd`). -/
theorem block_decomposition (nodes ord : List (List Nat)) (hperm : ord.Perm nodes)
    (hn : ∀ b ∈ nodes, b.Nodup) (kA kB : Nat → Bool) :
    (listInv ((ord.map (fun b => stablePart kA (stablePart kB b))).flatten)
        + listInv nodes.flatten
        + (nodes.map (fun b => wordInv (b.map kB))).sum
        + (ord.map (fun b => wordInv ((stablePart kB b).map kA))).sum
        + (pairCross ord + pairCross nodes)) % 2 = 0 := by
  have hF : listInv ((ord.map (fun b => stablePart kA (stablePart kB b))).flatten)
      = (ord.map (fun b => listInv (stablePart kA (stablePart kB b)))).sum
        + pairCross ord := by
    rw [listInv_flatten]
    have hm : List.map listInv (List.map (fun b => stablePart kA (stablePart kB b)) ord)
        = List.map (fun b => listInv (stablePart kA (stablePart kB b))) ord := by
      rw [List.map_map]
      exact List.map_congr_left (fun b _ => rfl)
    have hp : pairCross (List.map (fun b => stablePart kA (stablePart kB b)) ord)
        = pairCross ord := by
      have hm2 : List.map (fun b => stablePart kA (stablePart kB b)) ord
          = List.map (stablePart kA) (List.map (stablePart kB) ord) := by
        rw [List.map_map]
        exact List.map_congr_left (fun b _ => rfl)
      rw [hm2, pairCross_map_stablePart kA, pairCross_map_stablePart kB]
    rw [hm, hp]
  have hN : listInv nodes.flatten = (nodes.map listInv).sum + pairCross nodes :=
    listInv_flatten nodes
  have ha : ((ord.map (fun b => listInv (stablePart kA (stablePart kB b)))).sum
        + (ord.map (fun b => wordInv ((stablePart kB b).map kA))).sum) % 2
      = (ord.map (fun b => listInv (stablePart kB b))).sum % 2 :=
    sum_mod_two_congr _ _ _ ord
      (fun b hb => stablePart_parity kA _ (nodup_stablePart (hn b (hperm.mem_iff.mp hb))))
  have hb' : ((ord.map (fun b => listInv (stablePart kB b))).sum
        + (ord.map (fun b => wordInv (b.map kB))).sum) % 2
      = (ord.map listInv).sum % 2 :=
    sum_mod_two_congr _ _ _ ord
      (fun b hb => stablePart_parity kB _ (hn b (hperm.mem_iff.mp hb)))
  have hpermSum : (ord.map (fun b => wordInv (b.map kB))).sum
      = (nodes.map (fun b => wordInv (b.map kB))).sum :=
    perm_sum (hperm.map fun b => wordInv (b.map kB))
  have hpermInv : (ord.map listInv).sum = (nodes.map listInv).sum :=
    perm_sum (hperm.map listInv)
  rw [hF, hN]
  omega

/-- **L16 in the blueprint's own shape.**  If in addition the composite reordering has the
parity of a single even cycle (`listInv target + listInv source = 1`, the `succ P` step),
then `1 + E + Sum_v (invCount a_v + invCount b_v) = 0` with `E` the cross-block term. -/
theorem block_decomposition_blueprint (nodes ord : List (List Nat)) (hperm : ord.Perm nodes)
    (hn : ∀ b ∈ nodes, b.Nodup) (kA kB : Nat → Bool)
    (hcycle : (listInv ((ord.map (fun b => stablePart kA (stablePart kB b))).flatten)
        + listInv nodes.flatten) % 2 = 1) :
    (1 + (nodes.map (fun b => wordInv (b.map kB))).sum
        + (ord.map (fun b => wordInv ((stablePart kB b).map kA))).sum
        + (pairCross ord + pairCross nodes)) % 2 = 0 := by
  have h := block_decomposition nodes ord hperm hn kA kB
  omega

end PortInversion
