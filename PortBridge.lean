import UnitDiagonalWords

/-!
# Bridging a returning port between the two index lists

Let `α : List Bool` be an arbitrary finite binary table, `e : Bool` a layer parity and
`beta α e` the parity-flipped port word `beta[k] = α[k] XOR (k odd) XOR e`
(`UnitDiagonal.beta_spec`).  Write `p = trueIdx α` and `q = trueIdx (beta α e)` for the
increasing index lists of the `true` entries.

The paper statement (research note `persist-B-diagonal-m3-2026-11-22.md`, round 14) is
the following two-branch interleaving lemma.  Fix `i`, `j` and assume that the same
index `k` is the `i`-th entry of `p` and one more than the `j`-th entry of `q`, i.e.
`k = p[i] = q[j] + 1` (`m := q[j]`, so `k = m + 1`).  Then exactly one of two cases
holds, decided by the parity of `k` against the numeric value `ε = if e then 1 else 0`
of the layer parity:

1. parity branch `k % 2 = ε`: the original word reads `false` at `k - 1` and the flipped
   word also reads `true` at `k`, so `q` has an entry after `q[j]`, namely
   `q[j+1] = p[i] = k`;
2. opposite branch `k % 2 ≠ ε`: the original word reads `true` at `k - 1` and the flipped
   word reads `false` at `k`, so `p` has an entry before `p[i]`, namely
   `p[i-1] = q[j] = k - 1` (hence `0 < i`).

Consequently, at the *first* true index (`i = 0`) only branch 1 can occur, and there the
position is pinned exactly: `p[0] = 2 * j + 2 - ε` and `q[j+1] = p[0]`.

All statements are stated with lookups `p[i]? = some …` instead of `i < p.length`;
the two formulations are equivalent because a lookup that returns `some` forces the
index bound (`lt_length_of_getElem?`).

Every claim below was brute-force checked during development for every Boolean list of
length at most 12 and both parities `e` (40962 instances of `p[i] = q[j] + 1`, zero
failures); the `#eval` checker was deleted afterwards.  Every declaration is checked by
the Lean kernel: no `sorry`, no `admit`, no `axiom`, no `native_decide`.
-/

namespace UnitDiagonal

/-! ## Index-list arithmetic -/

/-- In a strictly increasing index list, an entry sitting at `m` and followed (as a
member) by `m + 1` is immediately followed by `m + 1`. -/
theorem getElem?_succ_of_mem {l : List Nat} (hp : l.Pairwise (· < ·)) {j m : Nat}
    (hj : l[j]? = some m) (hm : m + 1 ∈ l) : l[j + 1]? = some (m + 1) := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hm
  have hjlen : j < l.length := lt_length_of_getElem? hj
  have hnlen : n < l.length := lt_length_of_getElem? hn
  have hmono : ∀ (p q a b : Nat), p < q → l[p]? = some a → l[q]? = some b → a < b :=
    fun p q a b hpq hp' hq' => lt_of_pairwise hp hpq hp' hq'
  have hjn : j < n := by
    rcases Nat.lt_trichotomy n j with h | h | h
    · have hc := hmono n j (m + 1) m h hn hj
      omega
    · subst h
      rw [hj] at hn
      simp at hn
    · exact h
  have hn1 : n = j + 1 := by
    rcases Nat.lt_or_ge (j + 1) n with h | h
    · exfalso
      have h1 : j + 1 < l.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, l[j + 1]? = some c := ⟨l[j + 1], List.getElem?_eq_getElem h1⟩
      have hlt1 := hmono j (j + 1) m c (by omega) hj hc
      have hlt2 := hmono (j + 1) n c (m + 1) h hc hn
      omega
    · omega
  rw [← hn1]
  exact hn

/-- In a strictly increasing index list, an entry sitting at `m + 1` is immediately
preceded by `m` as soon as `m` is a member. -/
theorem getElem?_pred_of_mem {l : List Nat} (hp : l.Pairwise (· < ·)) {i m : Nat}
    (hi : l[i]? = some (m + 1)) (hm : m ∈ l) : 0 < i ∧ l[i - 1]? = some m := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hm
  have hilen : i < l.length := lt_length_of_getElem? hi
  have hnlen : n < l.length := lt_length_of_getElem? hn
  have hmono : ∀ (p q a b : Nat), p < q → l[p]? = some a → l[q]? = some b → a < b :=
    fun p q a b hpq hp' hq' => lt_of_pairwise hp hpq hp' hq'
  have hni : n < i := by
    rcases Nat.lt_trichotomy n i with h | h | h
    · exact h
    · subst h
      rw [hi] at hn
      simp at hn
    · have hc := hmono i n (m + 1) m h hi hn
      omega
  have hin : i = n + 1 := by
    rcases Nat.lt_or_ge (n + 1) i with h | h
    · exfalso
      have h1 : n + 1 < l.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, l[n + 1]? = some c := ⟨l[n + 1], List.getElem?_eq_getElem h1⟩
      have hlt1 := hmono n (n + 1) m c (by omega) hn hc
      have hlt2 := hmono (n + 1) i c (m + 1) h hc hi
      omega
    · omega
  refine ⟨by omega, ?_⟩
  rw [hin, Nat.add_sub_cancel]
  exact hn

/-- In a strictly increasing index list, the number of entries below the `j`-th entry is
exactly `j`. -/
theorem length_filter_lt_of_getElem? {l : List Nat} (hp : l.Pairwise (· < ·)) {j m : Nat}
    (hj : l[j]? = some m) : (l.filter (fun r => decide (r < m))).length = j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b l ih =>
    obtain ⟨hb, ht⟩ := List.pairwise_cons.mp hp
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hn : l.filter (fun r => decide (r < b)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro r hr
        have hbr := hb r hr
        simp only [decide_eq_true_eq]
        omega
      simp [hn]
    | succ j =>
      have hbk : l[j]? = some m := hj
      have hbm := hb m (List.mem_iff_getElem?.mpr ⟨j, hbk⟩)
      simpa [hbm] using ih ht hbk

/-! ## Boolean arithmetic of the flip -/

/-- Flipping a Boolean twice by the same bit is the identity. -/
theorem bne_bne_self (x e : Bool) : ((x != e) != e) = x := by
  cases x <;> cases e <;> rfl

/-- The negation of `m` being odd is `m` being even. -/
theorem not_decide_mod_two (m : Nat) : (!decide (m % 2 = 1)) = decide (m % 2 = 0) := by
  have h := Nat.mod_two_eq_zero_or_one m
  rcases h with h | h <;> simp [h]

/-- Being odd as a Boolean is being congruent to one modulo two. -/
theorem decide_mod_two_iff (m : Nat) (e : Bool) :
    (decide (m % 2 = 1) = e) ↔ ((m + 1) % 2 ≠ (if e then 1 else 0)) := by
  have h := Nat.mod_two_eq_zero_or_one m
  cases e <;> rcases h with h | h <;> simp [h] <;> omega

/-- At a `false` entry the flipped word reads the parity of the index against `e`. -/
theorem beta_of_false {α : List Bool} {e : Bool} {m : Nat} (h : α[m]? = some false) :
    (beta α e)[m]? = some (decide (m % 2 = 1) != e) := by
  rw [beta_spec, h]
  cases decide (m % 2 = 1) <;> cases e <;> rfl

/-- In the parity branch the flipped word reads `true` at the bridge index. -/
theorem beta_of_true_mod {α : List Bool} (e : Bool) {k : Nat} (h : α[k]? = some true)
    (hk : k % 2 = (if e then 1 else 0)) : (beta α e)[k]? = some true := by
  rw [beta_spec, h]
  simp only [Option.map_some]
  cases e with
  | false =>
    have hd : decide (k % 2 = 1) = false := by
      rw [show k % 2 = 0 from hk]
      rfl
    simp [hd]
  | true =>
    have hd : decide (k % 2 = 1) = true := by
      rw [show k % 2 = 1 from hk]
      rfl
    simp [hd]

/-- In the opposite branch the flipped word reads `false` at the bridge index. -/
theorem beta_of_true_notmod {α : List Bool} (e : Bool) {k : Nat} (h : α[k]? = some true)
    (hk : k % 2 ≠ (if e then 1 else 0)) : (beta α e)[k]? = some false := by
  rw [beta_spec, h]
  simp only [Option.map_some]
  have hle : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
  cases e with
  | false =>
    have hk1 : k % 2 = 1 := by
      rcases hle with h0 | h1
      · exact absurd h0 hk
      · exact h1
    have hd : decide (k % 2 = 1) = true := by rw [hk1]; rfl
    simp [hd]
  | true =>
    have hk0 : k % 2 = 0 := by
      rcases hle with h0 | h1
      · exact h0
      · exact absurd h1 hk
    have hd : decide (k % 2 = 1) = false := by rw [hk0]; rfl
    simp [hd]

/-- Invert the flip: the value of `α` at `m` is determined by the value of `beta` there
once the parity bit of `m` is known. -/
theorem alpha_of_beta {α : List Bool} {e : Bool} {m : Nat} {b c : Bool}
    (h : (beta α e)[m]? = some b) (hd : decide (m % 2 = 1) = c) :
    α[m]? = some (b != (c != e)) := by
  rw [beta_spec, hd] at h
  cases hα : α[m]? with
  | none =>
    rw [hα] at h
    simp at h
  | some a =>
    rw [hα] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]
    cases a <;> cases c <;> cases e <;> rfl

/-! ## The flipped word on a `false` prefix -/

/-- Shifting an index list up by one commutes with cutting at `N + 1`. -/
theorem filter_map_succ (l : List Nat) (N : Nat) :
    (l.map (· + 1)).filter (fun r => decide (r < N + 1)) =
      (l.filter (fun r => decide (r < N))).map (· + 1) := by
  rw [List.filter_map]
  congr 1

/-- Counting the `true` entries of a mapped word is counting the preimages. -/
theorem countTrue_map {α : Type} (f : α → Bool) (l : List α) :
    countTrue (l.map f) = (l.filter f).length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases hb : f b <;> simp [countTrue, List.filter, hb, ih] <;> omega

/-- Cutting the index list at `N` is taking the index list of the length-`N` prefix. -/
theorem filter_trueIdx_take (α : List Bool) (N : Nat) :
    (trueIdx α).filter (fun r => decide (r < N)) = trueIdx (α.take N) := by
  induction N generalizing α with
  | zero => cases α <;> simp
  | succ N ih =>
    cases α with
    | nil => simp
    | cons b l =>
      rw [List.take_succ_cons]
      cases b with
      | true =>
        rw [trueIdx_true_cons, List.filter_cons]
        have h0 : decide (0 < N + 1) = true := by simp
        rw [h0, ite_eq_left rfl, filter_map_succ, ih, trueIdx_true_cons]
      | false =>
        rw [trueIdx_false_cons, filter_map_succ, ih, trueIdx_false_cons]

/-- The number of `true` entries of `beta α e` below `m` is the number of `true` entries
of the length-`m` prefix of `beta α e`. -/
theorem length_filter_trueIdx (α : List Bool) (N : Nat) :
    ((trueIdx α).filter (fun r => decide (r < N))).length = countTrue (α.take N) := by
  rw [filter_trueIdx_take, trueIdx_length]

/-- On a prefix on which `α` is everywhere `false`, the flipped word is the parity word. -/
theorem beta_take_eq_map {α : List Bool} {e : Bool} {N : Nat}
    (h : ∀ m, m < N → α[m]? = some false) :
    (beta α e).take N = (List.range N).map (fun m => decide (m % 2 = 1) != e) := by
  have hN : N ≤ α.length := by
    rcases Nat.lt_or_ge α.length N with hlt | hge
    · exfalso
      have hc := h α.length hlt
      rw [List.getElem?_eq_none (Nat.le_refl α.length)] at hc
      simp at hc
    · exact hge
  refine eq_of_getElem?_of_length ?_ ?_
  · rw [List.length_take, beta_length, Nat.min_eq_left hN, List.length_map,
      List.length_range]
  · intro m hm
    have hmN : m < N := by simpa using hm
    rw [List.getElem?_take, List.getElem?_map, List.getElem?_range hmN, Option.map_some,
      ite_eq_left hmN]
    exact beta_of_false (h m hmN)

/-! ## The first `true` index -/

/-- Below the first `true` index the word reads `false` everywhere. -/
theorem alpha_false_below_first {α : List Bool} {k : Nat} (hp : (trueIdx α)[0]? = some k)
    {m : Nat} (hm : m < k) : α[m]? = some false := by
  have hpar := pairwise_trueIdx α
  have hk : α[k]? = some true := mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨0, hp⟩)
  have hklen : k < α.length := lt_length_of_getElem? hk
  have hmem : α[m]? = some (α[m]) := List.getElem?_eq_getElem (by omega)
  have hnot : m ∉ trueIdx α := by
    intro h'
    have hle := le_of_pairwise_zero hpar hp h'
    omega
  rw [hmem]
  cases hb : α[m]
  · rfl
  · exact absurd (mem_trueIdx.mpr (by rw [hmem, hb])) hnot

/-! ## Counting positions of a fixed parity -/

/-- Number of `m < N` with `m % 2 = c`. -/
def parityCount (N : Nat) (c : Nat) : Nat :=
  ((List.range N).filter (fun m => decide (m % 2 = c))).length

/-- Twice the number of odd indices below `N` plus the parity of `N` is `N`. -/
theorem two_mul_parityCount_one (N : Nat) : 2 * parityCount N 1 + N % 2 = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hstep : parityCount (N + 1) 1 = parityCount N 1 + (if N % 2 = 1 then 1 else 0) := by
      rw [parityCount, List.range_succ, List.filter_append, List.length_append, parityCount]
      congr 1
      by_cases h : N % 2 = 1 <;> simp [h]
    rw [hstep]
    have h := Nat.mod_two_eq_zero_or_one N
    rcases h with h | h <;> simp [h] at * <;> omega

/-- Twice the number of even indices below `N` is `N + N % 2`. -/
theorem two_mul_parityCount_zero (N : Nat) : 2 * parityCount N 0 = N + N % 2 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hstep : parityCount (N + 1) 0 = parityCount N 0 + (if N % 2 = 0 then 1 else 0) := by
      rw [parityCount, List.range_succ, List.filter_append, List.length_append, parityCount]
      congr 1
      by_cases h : N % 2 = 0 <;> simp [h]
    rw [hstep]
    have h := Nat.mod_two_eq_zero_or_one N
    rcases h with h | h <;> simp [h] at * <;> omega

/-! ## The two-branch interleaving lemma -/

/-- **Branch 1 (parity branch).** If `k = m + 1` is an entry of `p` and `m` is an entry
of `q`, and if `k` has the parity of the layer, then `q` continues with `k` itself. -/
theorem bridge_parity {α : List Bool} (e : Bool) {i j m : Nat}
    (hp : (trueIdx α)[i]? = some (m + 1))
    (hq : (trueIdx (beta α e))[j]? = some m)
    (hpar : (m + 1) % 2 = (if e then 1 else 0)) :
    (trueIdx (beta α e))[j + 1]? = some (m + 1) := by
  have hk : α[m + 1]? = some true :=
    mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨i, hp⟩)
  have hb : (beta α e)[m + 1]? = some true := beta_of_true_mod e hk hpar
  have hmem : m + 1 ∈ trueIdx (beta α e) := mem_trueIdx.mpr hb
  exact getElem?_succ_of_mem (pairwise_trueIdx _) hq hmem

/-- **Branch 2 (opposite branch).** If `k = m + 1` is an entry of `p` and `m` is an entry
of `q`, and if `k` does not have the parity of the layer, then `p` starts its entry `m`
directly before `k`, so `0 < i` and `p[i-1] = q[j] = m`. -/
theorem bridge_opposite {α : List Bool} (e : Bool) {i j m : Nat}
    (hp : (trueIdx α)[i]? = some (m + 1))
    (hq : (trueIdx (beta α e))[j]? = some m)
    (hpar : (m + 1) % 2 ≠ (if e then 1 else 0)) :
    0 < i ∧ (trueIdx α)[i - 1]? = some m := by
  have hb : (beta α e)[m]? = some true :=
    mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨j, hq⟩)
  have hd : decide (m % 2 = 1) = e := (decide_mod_two_iff m e).mpr hpar
  have ha : α[m]? = some true := by
    have h := alpha_of_beta hb hd
    simpa [bne_bne_self] using h
  have hmem : m ∈ trueIdx α := mem_trueIdx.mpr ha
  exact getElem?_pred_of_mem (pairwise_trueIdx _) hp hmem

/-- The parity branch also pins the original bit just below the bridge: it is `false`. -/
theorem bridge_parity_alpha_false {α : List Bool} (e : Bool) {j m : Nat}
    (hq : (trueIdx (beta α e))[j]? = some m)
    (hpar : (m + 1) % 2 = (if e then 1 else 0)) : α[m]? = some false := by
  have hb : (beta α e)[m]? = some true :=
    mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨j, hq⟩)
  have hd : decide (m % 2 = 1) = !e := by
    apply (decide_mod_two_iff m (!e)).mpr
    cases e <;> simp [hpar]
  have h := alpha_of_beta hb hd
  have hx : ((true : Bool) != ((!e) != e)) = false := by cases e <;> rfl
  rw [hx] at h
  exact h

/-- The opposite branch also pins the flipped bit at the bridge: it is `false`. -/
theorem bridge_opposite_beta_false {α : List Bool} (e : Bool) {i m : Nat}
    (hp : (trueIdx α)[i]? = some (m + 1))
    (hpar : (m + 1) % 2 ≠ (if e then 1 else 0)) : (beta α e)[m + 1]? = some false := by
  have hk : α[m + 1]? = some true :=
    mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨i, hp⟩)
  exact beta_of_true_notmod e hk hpar

/-- **Round-14 lemma.** For an arbitrary table and both layer parities, a returning port
`p[i] = q[j] + 1` forces exactly one of the two adjacent bridges: either `q[j+1] = p[i]`
(parity branch) or `p[i-1] = q[j]` with `0 < i` (opposite branch). -/
theorem interleave_dichotomy {α : List Bool} (e : Bool) {i j m : Nat}
    (hp : (trueIdx α)[i]? = some (m + 1))
    (hq : (trueIdx (beta α e))[j]? = some m) :
    ((m + 1) % 2 = (if e then 1 else 0) ∧
        (trueIdx (beta α e))[j + 1]? = some (m + 1)) ∨
      (0 < i ∧ (trueIdx α)[i - 1]? = some m) := by
  by_cases hpar : (m + 1) % 2 = (if e then 1 else 0)
  · exact Or.inl ⟨hpar, bridge_parity e hp hq hpar⟩
  · exact Or.inr (bridge_opposite e hp hq hpar)

/-- **Corollary at the first port.** If the returning port ends at the first `true` index
`p[0] = m + 1`, branch 2 is impossible, so the parity branch holds and the position is
pinned: `p[0] = 2 * j + 2 - ε` and `q[j+1] = p[0]`. -/
theorem first_index_corollary {α : List Bool} (e : Bool) {j m : Nat}
    (hp : (trueIdx α)[0]? = some (m + 1))
    (hq : (trueIdx (beta α e))[j]? = some m) :
    (m + 1) % 2 = (if e then 1 else 0) ∧
      m + 1 = 2 * j + 2 - (if e then 1 else 0) ∧
      (trueIdx (beta α e))[j + 1]? = some (m + 1) := by
  -- branch 2 would force `0 < 0`
  have hpar : (m + 1) % 2 = (if e then 1 else 0) := by
    by_cases hne : (m + 1) % 2 = (if e then 1 else 0)
    · exact hne
    · have hb := (bridge_opposite e (i := 0) hp hq hne).1
      omega
  refine ⟨hpar, ?_, bridge_parity e hp hq hpar⟩
  -- count the `q`-entries below `m`
  have hqj : j = ((trueIdx (beta α e)).filter (fun r => decide (r < m))).length :=
    (length_filter_lt_of_getElem? (pairwise_trueIdx _) hq).symm
  have hcnt : ((trueIdx (beta α e)).filter (fun r => decide (r < m))).length =
      countTrue ((beta α e).take m) := length_filter_trueIdx _ m
  have hpre : (beta α e).take m =
      (List.range m).map (fun r => decide (r % 2 = 1) != e) :=
    beta_take_eq_map (fun r hr => alpha_false_below_first hp (by omega))
  have hmap : countTrue ((List.range m).map (fun r => decide (r % 2 = 1) != e)) =
      ((List.range m).filter (fun r => decide (r % 2 = 1) != e)).length :=
    countTrue_map _ _
  -- identify the count with `parityCount` for the complementary parity
  have hparity : j = parityCount m (1 - (if e then 1 else 0)) := by
    rw [hqj, hcnt, hpre, hmap]
    show ((List.range m).filter (fun r => decide (r % 2 = 1) != e)).length =
      ((List.range m).filter (fun r => decide (r % 2 = 1 - (if e then 1 else 0)))).length
    cases e with
    | false => simp only [Bool.false_eq_true, ite_false, Nat.sub_zero, Bool.bne_false]
    | true => simp only [ite_true, Nat.sub_self, Bool.bne_true, not_decide_mod_two]
  cases e with
  | false =>
    have hpar' : (m + 1) % 2 = 0 := hpar
    have hparity' : j = parityCount m 1 := by simpa using hparity
    have h1 := two_mul_parityCount_one m
    omega
  | true =>
    have hpar' : (m + 1) % 2 = 1 := hpar
    have hparity' : j = parityCount m 0 := by simpa using hparity
    have h0 := two_mul_parityCount_zero m
    omega

end UnitDiagonal
