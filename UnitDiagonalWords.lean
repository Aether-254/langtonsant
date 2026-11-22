import UnitDiagonalPorts

/-!
# Unit diagonal words: abstract word lemmas

This file collects the purely combinatorial word lemmas used by the unit-diagonal
width analysis.  Everything is stated for arbitrary `List Bool` words of arbitrary
length; no length bound is ever assumed, every bound is derived from
`even_layer` / `odd_layer` and from the combinatorics of the index list `trueIdx`.

* `L17`: on an odd layer with `countTrue α = 1` and `countTrue (beta α true) = 1`
  the length of `α` is not `2` (width two is impossible), and in that situation
  `α.length + α.length % 2 = 4 * evenTrue α`.
* `L18`: on an odd layer with both counts equal to one, a nonempty `α` is one of
  `[1,0,0]`, `[1,0,0,0]`, `[0,0,1]`, `[0,0,1,0]`.
* `L21/L22`: on the even layer, if the two index lists have the same length `c`
  with `c = 2` or `c = 3` and the shifted first-index relation
  `p[0] = q[1] + 1` holds, then `c = 3` and `α ∈ {00001101, 000011010}`.
* `L23`: the index data of the two surviving words.

Every declaration is checked by the Lean kernel: no `sorry`, no `admit`, no `axiom`,
no `native_decide`.  The finite case splits use `decide` on closed goals over `Bool`
(kernel evaluation), never `native_decide`.
-/

namespace UnitDiagonal

/-! ## Index lists -/

/-- The increasing list of indices at which a Boolean word reads `true`. -/
def trueIdx : List Bool → List Nat
  | [] => []
  | true :: l => 0 :: (trueIdx l).map (· + 1)
  | false :: l => (trueIdx l).map (· + 1)

/-- The increasing list of indices at which a Boolean word reads `false`. -/
def falseIdx (l : List Bool) : List Nat := trueIdx (l.map (!·))

@[simp] theorem trueIdx_nil : trueIdx [] = [] := rfl

@[simp] theorem trueIdx_true_cons (l : List Bool) :
    trueIdx (true :: l) = 0 :: (trueIdx l).map (· + 1) := rfl

@[simp] theorem trueIdx_false_cons (l : List Bool) :
    trueIdx (false :: l) = (trueIdx l).map (· + 1) := rfl

/-- A lookup index is smaller than the length of the list. -/
theorem lt_length_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := by
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · exact hlt
  · have hz : l[i]? = none := List.getElem?_eq_none hge
    rw [h] at hz
    cases hz

/-- Membership in `trueIdx` is being `true` at that index. -/
theorem mem_trueIdx {α : List Bool} {k : Nat} : k ∈ trueIdx α ↔ α[k]? = some true := by
  induction α generalizing k with
  | nil => simp
  | cons b l ih =>
    have hstep : ∀ j : Nat, (j + 1 ∈ (trueIdx l).map (· + 1)) ↔ j ∈ trueIdx l := by
      intro j
      rw [List.mem_map]
      constructor
      · rintro ⟨x, hx, hx'⟩
        have hxj : x = j := by omega
        rwa [hxj] at hx
      · intro hx
        exact ⟨j, hx, rfl⟩
    cases b with
    | true =>
      cases k with
      | zero => simp
      | succ j => simp [hstep, ih]
    | false =>
      cases k with
      | zero => simp
      | succ j => simp [hstep, ih]

/-- The number of indices at which the word reads `true`. -/
theorem trueIdx_length (α : List Bool) : (trueIdx α).length = countTrue α := by
  induction α with
  | nil => rfl
  | cons b l ih => cases b <;> simp [countTrue, ih] <;> omega

/-- The index list is strictly increasing. -/
theorem pairwise_trueIdx (α : List Bool) : (trueIdx α).Pairwise (· < ·) := by
  induction α with
  | nil => simp
  | cons b l ih =>
    cases b with
    | true =>
      refine List.Pairwise.cons ?_ ?_
      · intro a' ha'
        obtain ⟨x, -, hx⟩ := List.mem_map.mp ha'
        omega
      · rw [List.pairwise_map]
        exact ih.imp (fun h => by omega)
    | false =>
      rw [trueIdx_false_cons, List.pairwise_map]
      exact ih.imp (fun h => by omega)

/-! ## Monotonicity of a pairwise increasing index list -/

/-- A strictly increasing list is strictly increasing at every pair of indices. -/
theorem lt_of_pairwise {l : List Nat} (h : l.Pairwise (· < ·)) {i j : Nat} (hij : i < j)
    {a b : Nat} (hi : l[i]? = some a) (hj : l[j]? = some b) : a < b := by
  have hi' : i < l.length := lt_length_of_getElem? hi
  have hj' : j < l.length := lt_length_of_getElem? hj
  have hia : l[i] = a := Option.some.inj ((List.getElem?_eq_getElem hi').symm.trans hi)
  have hjb : l[j] = b := Option.some.inj ((List.getElem?_eq_getElem hj').symm.trans hj)
  have hpair := (List.pairwise_iff_getElem.mp h) i j hi' hj' hij
  rwa [hia, hjb] at hpair

/-- The first element of a strictly increasing list is its minimum. -/
theorem le_of_pairwise_zero {l : List Nat} (h : l.Pairwise (· < ·)) {a k : Nat}
    (h0 : l[0]? = some a) (hk : k ∈ l) : a ≤ k := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
  cases i with
  | zero => exact Nat.le_of_eq (Option.some.inj (h0.symm.trans hi))
  | succ j =>
    have hlt := lt_of_pairwise h (Nat.zero_lt_succ j) h0 hi
    omega

/-! ## Counting indices -/

/-- A list of distinct indices, all of which are indices of `l`, is no longer than `l`. -/
theorem length_le_of_forall_mem {l : List Nat} :
    ∀ ks : List Nat, ks.Nodup → (∀ k, k ∈ ks → k ∈ l) → ks.length ≤ l.length
  | [], _, _ => by simp
  | a :: ks, hnd, hsub => by
    have hnd' : ks.Nodup := (List.nodup_cons.mp hnd).2
    have ha_not : a ∉ ks := (List.nodup_cons.mp hnd).1
    have ha : a ∈ l := hsub a List.mem_cons_self
    obtain ⟨s, t, ht⟩ := List.mem_iff_append.mp ha
    have hsub' : ∀ k, k ∈ ks → k ∈ s ++ t := by
      intro k hk
      have hk2 : k ∈ l := hsub k (List.mem_cons_of_mem a hk)
      rw [ht] at hk2
      have hne : k ≠ a := fun h => ha_not (h ▸ hk)
      rcases List.mem_append.mp hk2 with h' | h'
      · exact List.mem_append_left _ h'
      · rcases List.mem_cons.mp h' with h'' | h''
        · exact absurd h'' hne
        · exact List.mem_append_right _ h''
    have ih := length_le_of_forall_mem ks hnd' hsub'
    rw [ht]
    simp only [List.length_cons, List.length_append] at ih ⊢
    omega

/-! ## The parity flip `beta` at a fixed index -/

/-- At an even-layer index with `α[k] = false`, the flipped word reads `k` odd. -/
theorem beta_false_of_alpha_false {α : List Bool} {k : Nat} (h : α[k]? = some false) :
    (beta α false)[k]? = some (decide (k % 2 = 1)) := by
  rw [beta_spec, h]
  cases hd : decide (k % 2 = 1) <;> simp

/-- Conversely, an even-layer index that reads `false` in `beta` reads `k` odd in `α`. -/
theorem alpha_eq_decide_of_beta_false {α : List Bool} {k : Nat}
    (h : (beta α false)[k]? = some false) : α[k]? = some (decide (k % 2 = 1)) := by
  rw [beta_spec] at h
  cases hk : α[k]? with
  | none => rw [hk] at h; simp at h
  | some a =>
    rw [hk] at h
    cases a <;> cases hd : decide (k % 2 = 1) <;> simp [hd] at h ⊢

/-- At an even index with `α[k] = true`, the even-layer flipped word reads `true`. -/
theorem beta_true_of_alpha_true_even {α : List Bool} {k : Nat} (h : α[k]? = some true)
    (hk : k % 2 = 0) : (beta α false)[k]? = some true := by
  rw [beta_spec, h]
  cases hd : decide (k % 2 = 1) with
  | true =>
    have : k % 2 = 1 := of_decide_eq_true hd
    omega
  | false => rfl

/-- A strictly increasing list of length three admits only its three entries. -/
theorem eq_one_of_mem_length_three {l : List Nat} {a₀ a₁ a₂ v : Nat}
    (h0 : l[0]? = some a₀) (h1 : l[1]? = some a₁) (h2 : l[2]? = some a₂)
    (hlen : l.length = 3) (hmem : v ∈ l) : v = a₀ ∨ v = a₁ ∨ v = a₂ := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hj3 : j < 3 := by rw [← hlen]; exact lt_length_of_getElem? hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · exact Or.inl (Option.some.inj (h0.symm.trans hj)).symm
  · exact Or.inr (Or.inl (Option.some.inj (h1.symm.trans hj)).symm)
  · exact Or.inr (Or.inr (Option.some.inj (h2.symm.trans hj)).symm)

/-- Two lists with pointwise equal lookups and equal lengths are equal. -/
theorem eq_of_getElem?_of_length {w l : List Bool} (hlen : l.length = w.length)
    (h : ∀ k, k < w.length → l[k]? = w[k]?) : l = w := by
  refine List.ext_getElem? (fun k => ?_)
  by_cases hk : k < w.length
  · exact h k hk
  · have h1 : l[k]? = none := List.getElem?_eq_none (by omega)
    have h2 : w[k]? = none := List.getElem?_eq_none (by omega)
    rw [h1, h2]

/-! ## L17: width two is impossible on an odd layer -/

/-- On an odd layer with `I = J = 1` the counting identity reads `n + n % 2 = 4 e`. -/
theorem odd_layer_arith (α : List Bool) (hI : countTrue α = 1)
    (hJ : countTrue (beta α true) = 1) :
    α.length + α.length % 2 = 4 * evenTrue α := by
  have h := odd_layer α
  rw [hI, hJ] at h
  omega

/-- **L17.** A width-two word cannot have a single port on each side of an odd layer. -/
theorem odd_layer_length_ne_two (α : List Bool) (hI : countTrue α = 1)
    (hJ : countTrue (beta α true) = 1) : α.length ≠ 2 := by
  intro h2
  have h := odd_layer_arith α hI hJ
  rw [h2] at h
  omega

/-! ## L18: the odd-layer words with a single port on each side -/

/-- The number of `true` entries at even indices never exceeds the total count. -/
theorem evenTrue_le_countTrue (α : List Bool) : evenTrue α ≤ countTrue α := by
  induction α using evenTrue.induct with
  | case1 => simp [evenTrue, countTrue]
  | case2 => simp [evenTrue, countTrue]
  | case3 a ha =>
    cases a
    · simp [evenTrue, countTrue]
    · exact absurd rfl ha
  | case4 a b rest ih =>
    cases a <;> cases b <;> simp [evenTrue, countTrue] at ih ⊢ <;> omega

/-- **L18, length bound.** A nonempty odd-layer word with `I = J = 1` has length three or four. -/
theorem odd_layer_length_three_or_four (α : List Bool) (hI : countTrue α = 1)
    (hJ : countTrue (beta α true) = 1) (hne : α ≠ []) :
    α.length = 3 ∨ α.length = 4 := by
  have h := odd_layer_arith α hI hJ
  have he := evenTrue_le_countTrue α
  have hn0 : α.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.mp h0)
  omega

/-- Every list of length three is a three-entry list. -/
theorem exists_eq_three {α : List Bool} (h : α.length = 3) : ∃ a b c, α = [a, b, c] := by
  cases α with
  | nil => simp at h
  | cons a r =>
    cases r with
    | nil => simp at h
    | cons b r2 =>
      cases r2 with
      | nil => simp at h
      | cons c r3 =>
        have hr : r3 = [] := by
          have hz := h
          simp at hz
          exact hz
        subst hr
        exact ⟨a, b, c, rfl⟩

/-- Every list of length four is a four-entry list. -/
theorem exists_eq_four {α : List Bool} (h : α.length = 4) : ∃ a b c d, α = [a, b, c, d] := by
  cases α with
  | nil => simp at h
  | cons a r =>
    cases r with
    | nil => simp at h
    | cons b r2 =>
      cases r2 with
      | nil => simp at h
      | cons c r3 =>
        cases r3 with
        | nil => simp at h
        | cons d r4 =>
          have hr : r4 = [] := by
            have hz := h
            simp at hz
            exact hz
          subst hr
          exact ⟨a, b, c, d, rfl⟩

/-- Closed check: the length-three odd-layer words with . -/
theorem odd3_cases : ∀ a b c : Bool, countTrue [a, b, c] = 1 →
    countTrue (beta [a, b, c] true) = 1 →
    (([a, b, c] : List Bool) = [true, false, false] ∨
      ([a, b, c] : List Bool) = [false, false, true]) := by decide

/-- Closed check: the length-four odd-layer words with . -/
theorem odd4_cases : ∀ a b c d : Bool, countTrue [a, b, c, d] = 1 →
    countTrue (beta [a, b, c, d] true) = 1 →
    (([a, b, c, d] : List Bool) = [true, false, false, false] ∨
      ([a, b, c, d] : List Bool) = [false, false, true, false]) := by decide

/-- **L18.** A nonempty odd-layer word with  is one of four words. -/
theorem odd_layer_single_true (α : List Bool) (hI : countTrue α = 1)
    (hJ : countTrue (beta α true) = 1) (hne : α ≠ []) :
    α = [true, false, false] ∨ α = [true, false, false, false] ∨
      α = [false, false, true] ∨ α = [false, false, true, false] := by
  rcases odd_layer_length_three_or_four α hI hJ hne with h3 | h4
  · obtain ⟨a, b, c, rfl⟩ := exists_eq_three h3
    rcases odd3_cases a b c hI hJ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨a, b, c, d, rfl⟩ := exists_eq_four h4
    rcases odd4_cases a b c d hI hJ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

/-! ## L23 data: the two surviving words -/

/-- The width eight word `00001101`. -/
def W8 : List Bool := [false, false, false, false, true, true, false, true]

/-- The width nine word `000011010`. -/
def W9 : List Bool := [false, false, false, false, true, true, false, true, false]

theorem W8_trueIdx : trueIdx W8 = [4, 5, 7] := by decide

theorem W8_beta_trueIdx : trueIdx (beta W8 false) = [1, 3, 4] := by decide

theorem W8_beta_falseIdx : falseIdx (beta W8 false) = [0, 2, 5, 6, 7] := by decide

theorem W8_falseIdx : falseIdx W8 = [0, 1, 2, 3, 6] := by decide

theorem W9_trueIdx : trueIdx W9 = [4, 5, 7] := by decide

theorem W9_beta_trueIdx : trueIdx (beta W9 false) = [1, 3, 4] := by decide

theorem W9_beta_falseIdx : falseIdx (beta W9 false) = [0, 2, 5, 6, 7, 8] := by decide

theorem W9_falseIdx : falseIdx W9 = [0, 1, 2, 3, 6, 8] := by decide

/-! ## L21 / L22: the even-layer words -/

/-- **L21/L22.** On the even layer, if the two index lists have a common length `c`
with `c = 2` or `c = 3` and the shifted first-index relation `p[0] = q[1] + 1` holds,
then `c = 3` and `α` is `00001101` or `000011010`. -/
theorem even_two_or_three (α : List Bool) (c a b : Nat)
    (hp_len : (trueIdx α).length = c)
    (hq_len : (trueIdx (beta α false)).length = c)
    (hc : c = 2 ∨ c = 3)
    (hq_two : 2 ≤ (trueIdx (beta α false)).length)
    (hp_one : 1 ≤ (trueIdx α).length)
    (hp0 : (trueIdx α)[0]? = some a)
    (hq1 : (trueIdx (beta α false))[1]? = some b)
    (hab : a = b + 1) :
    c = 3 ∧ (α = W8 ∨ α = W9) := by
  -- counting facts
  have hc_le : c ≤ 3 := by rcases hc with h | h <;> omega
  have hI : countTrue α = c := by rw [← hp_len, trueIdx_length]
  have hJ : countTrue (beta α false) = c := by rw [← hq_len, trueIdx_length]
  have hpair_p : (trueIdx α).Pairwise (· < ·) := pairwise_trueIdx α
  have hpair_q : (trueIdx (beta α false)).Pairwise (· < ·) := pairwise_trueIdx (beta α false)
  -- basic index facts
  have hq_one : 1 < (trueIdx (beta α false)).length := Nat.lt_of_lt_of_le (by decide) hq_two
  have hp_zero : 0 < (trueIdx α).length := Nat.lt_of_lt_of_le (by decide) hp_one
  have hq0 : ∃ a0, (trueIdx (beta α false))[0]? = some a0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hqb : b ∈ trueIdx (beta α false) := List.mem_iff_getElem?.mpr ⟨1, hq1⟩
  have hba : b < a := by rw [hab]; omega
  have hpa : a ∈ trueIdx α := List.mem_iff_getElem?.mpr ⟨0, hp0⟩
  have ha_true : α[a]? = some true := mem_trueIdx.mp hpa
  have han : a < α.length := lt_length_of_getElem? ha_true
  -- `α` is false strictly below its first true index
  have hbelow : ∀ k, k < a → α[k]? = some false := by
    intro k hk
    have hklen : k < α.length := by omega
    have hknot : k ∉ trueIdx α := by
      intro hmem
      have hle := le_of_pairwise_zero hpair_p hp0 hmem
      omega
    have hkem : α[k]? = some α[k] := List.getElem?_eq_getElem hklen
    have hne : α[k] ≠ true := by
      intro h
      exact hknot (mem_trueIdx.mpr (by rw [hkem, h]))
    rw [hkem]
    cases hv : α[k] <;> simp_all
  -- hence on the even layer the flipped word reads exactly the odd indices below `a`
  have hqiff : ∀ k, k < a → (k ∈ trueIdx (beta α false) ↔ k % 2 = 1) := by
    intro k hk
    rw [mem_trueIdx, beta_false_of_alpha_false (hbelow k hk)]
    simp
  have hmem_odd : ∀ k, k < a → k % 2 = 1 → k ∈ trueIdx (beta α false) :=
    fun k hk hodd => (hqiff k hk).mpr hodd
  have hbodd : b % 2 = 1 := (hqiff b hba).mp hqb
  have haeven : a % 2 = 0 := by omega
  -- `a ≥ 2` and `a ≠ 2`
  have ha_ge2 : 2 ≤ a := by omega
  have ha_ne2 : a ≠ 2 := by
    intro h2
    obtain ⟨a0, ha0⟩ := hq0
    have hb1 : b = 1 := by omega
    have hlt : a0 < b := lt_of_pairwise hpair_q (by omega : 0 < 1) ha0 hq1
    have ha0z : a0 = 0 := by omega
    have hmem0 : (0 : Nat) ∈ trueIdx (beta α false) := by
      rw [List.mem_iff_getElem?]
      exact ⟨0, by rw [ha0, ha0z]⟩
    have hodd0 := (hqiff 0 (by omega)).mp hmem0
    omega
  have ha_ge4 : 4 ≤ a := by omega
  -- `a ≤ 6` (else four odd indices already exhaust `q`)
  have ha_le6 : a ≤ 6 := by
    rcases Nat.lt_or_ge 7 a with h7 | h7
    · exfalso
      have hsub : ∀ k, k ∈ ([1, 3, 5, 7] : List Nat) → k ∈ trueIdx (beta α false) := by
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hmem_odd 1 (by omega) (by decide)
        · rcases List.mem_cons.mp hk with rfl | hk
          · exact hmem_odd 3 (by omega) (by decide)
          · rcases List.mem_cons.mp hk with rfl | hk
            · exact hmem_odd 5 (by omega) (by decide)
            · rcases List.mem_cons.mp hk with rfl | hk
              · exact hmem_odd 7 (by omega) (by decide)
              · exact absurd hk List.not_mem_nil
      have hnd : ([1, 3, 5, 7] : List Nat).Nodup := by decide
      have hlen := length_le_of_forall_mem [1, 3, 5, 7] hnd hsub
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    · omega
  -- `a` itself is a true index of the flipped word
  have ha_q : a ∈ trueIdx (beta α false) := by
    rw [mem_trueIdx]
    exact beta_true_of_alpha_true_even ha_true haeven
  -- therefore `a = 4` and `b = 3`
  have ha_ne6 : a ≠ 6 := by
    intro h6
    have hsub : ∀ k, k ∈ ([1, 3, 5, 6] : List Nat) → k ∈ trueIdx (beta α false) := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hmem_odd 1 (by omega) (by decide)
      · rcases List.mem_cons.mp hk with rfl | hk
        · exact hmem_odd 3 (by omega) (by decide)
        · rcases List.mem_cons.mp hk with rfl | hk
          · exact hmem_odd 5 (by omega) (by decide)
          · rcases List.mem_cons.mp hk with rfl | hk
            · rw [← h6]; exact ha_q
            · exact absurd hk List.not_mem_nil
    have hnd : ([1, 3, 5, 6] : List Nat).Nodup := by decide
    have hlen := length_le_of_forall_mem [1, 3, 5, 6] hnd hsub
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have ha4 : a = 4 := by omega
  have hb3 : b = 3 := by omega
  -- `q` has exactly the three indices `1, 3, 4`
  have hc3 : c = 3 := by
    have hsub : ∀ k, k ∈ ([1, 3, 4] : List Nat) → k ∈ trueIdx (beta α false) := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hmem_odd 1 (by omega) (by decide)
      · rcases List.mem_cons.mp hk with rfl | hk
        · exact hmem_odd 3 (by omega) (by decide)
        · rcases List.mem_cons.mp hk with rfl | hk
          · rw [← ha4]; exact ha_q
          · exact absurd hk List.not_mem_nil
    have hnd : ([1, 3, 4] : List Nat).Nodup := by decide
    have hlen := length_le_of_forall_mem [1, 3, 4] hnd hsub
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  -- `q` is exhausted, so above index four the flipped word is false
  have hup : ∀ k, 4 < k → k < α.length → (beta α false)[k]? = some false := by
    intro k hk hklen
    have hblen : k < (beta α false).length := by rwa [beta_length]
    have hnot : k ∉ trueIdx (beta α false) := by
      intro hmem
      have hsub : ∀ j, j ∈ ([1, 3, 4, k] : List Nat) → j ∈ trueIdx (beta α false) := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hmem_odd 1 (by omega) (by decide)
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact hmem_odd 3 (by omega) (by decide)
          · rcases List.mem_cons.mp hj with rfl | hj
            · rw [← ha4]; exact ha_q
            · rcases List.mem_cons.mp hj with rfl | hj
              · exact hmem
              · exact absurd hj List.not_mem_nil
      have hnd : ([1, 3, 4, k] : List Nat).Nodup := by
        simp [List.nodup_cons]
        omega
      have hlen := length_le_of_forall_mem [1, 3, 4, k] hnd hsub
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    rw [mem_trueIdx] at hnot
    have hkem : (beta α false)[k]? = some ((beta α false)[k]) := List.getElem?_eq_getElem hblen
    rw [hkem] at hnot ⊢
    cases hv : (beta α false)[k] <;> simp_all
  -- above index four the original word is exactly the parity word
  have halpha_up : ∀ k, 4 < k → k < α.length → α[k]? = some (decide (k % 2 = 1)) :=
    fun k hk hklen => alpha_eq_decide_of_beta_false (hup k hk hklen)
  -- the first index list is `4, a1, a2`
  have hplen : (trueIdx α).length = 3 := by omega
  have hp0' : (trueIdx α)[0]? = some 4 := by rw [ha4] at hp0; exact hp0
  obtain ⟨a1, ha1⟩ : ∃ a1, (trueIdx α)[1]? = some a1 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have h4a1 : 4 < a1 := by
    have hlt := lt_of_pairwise hpair_p (by omega : 0 < 1) hp0' ha1
    omega
  have ha1n : a1 < α.length := by
    have hmem1 : a1 ∈ trueIdx α := List.mem_iff_getElem?.mpr ⟨1, ha1⟩
    exact lt_length_of_getElem? (mem_trueIdx.mp hmem1)
  obtain ⟨a2, ha2⟩ : ∃ a2, (trueIdx α)[2]? = some a2 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have h5a2 : 5 < a2 := by
    have h1 : 4 < a2 := by
      have hlt := lt_of_pairwise hpair_p (by omega : 0 < 2) hp0' ha2
      omega
    have h2 : a1 < a2 := lt_of_pairwise hpair_p (by omega : 1 < 2) ha1 ha2
    omega
  have ha2n : a2 < α.length := by
    have hmem2 : a2 ∈ trueIdx α := List.mem_iff_getElem?.mpr ⟨2, ha2⟩
    exact lt_length_of_getElem? (mem_trueIdx.mp hmem2)
  -- index five is true, and it is `a1`
  have h5n : 5 < α.length := by omega
  have h5p : (5 : Nat) ∈ trueIdx α := by
    rw [mem_trueIdx, halpha_up 5 (by omega) h5n]
    rfl
  have ha1eq : a1 = 5 := by
    rcases eq_one_of_mem_length_three hp0' ha1 ha2 hplen h5p with h | h | h
    · omega
    · exact h.symm
    · omega
  -- the length is at least eight
  have hn8 : 8 ≤ α.length := by
    rcases Nat.lt_or_ge α.length 8 with hlt | hge
    · exfalso
      have ha2_6 : a2 = 6 := by omega
      have h6n : 6 < α.length := by omega
      have hα6 := halpha_up 6 (by omega : 4 < 6) h6n
      have hmem2 : a2 ∈ trueIdx α := List.mem_iff_getElem?.mpr ⟨2, ha2⟩
      have htrue : α[a2]? = some true := mem_trueIdx.mp hmem2
      rw [ha2_6, hα6] at htrue
      simp at htrue
    · omega
  -- index seven is true, and it is `a2`
  have h7n : 7 < α.length := by omega
  have h7p : (7 : Nat) ∈ trueIdx α := by
    rw [mem_trueIdx, halpha_up 7 (by omega) h7n]
    rfl
  have ha2eq : a2 = 7 := by
    rcases eq_one_of_mem_length_three hp0' ha1 ha2 hplen h7p with h | h | h
    · omega
    · omega
    · exact h.symm
  -- so the length is at most nine
  have hn9 : α.length ≤ 9 := by
    rcases Nat.lt_or_ge 9 α.length with hlt | hge
    · exfalso
      have h9n : 9 < α.length := hlt
      have h9p : (9 : Nat) ∈ trueIdx α := by
        rw [mem_trueIdx, halpha_up 9 (by omega) h9n]
        rfl
      rcases eq_one_of_mem_length_three hp0' ha1 ha2 hplen h9p with h | h | h <;> omega
    · omega
  -- the two remaining lengths determine the two words
  refine ⟨hc3, ?_⟩
  rcases (show α.length = 8 ∨ α.length = 9 by omega) with hn | hn
  · left
    have hlen : α.length = W8.length := by rw [hn]; rfl
    refine eq_of_getElem?_of_length hlen ?_
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
      simp [W8] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [W8] using hbelow 0 (by omega)
    · simpa [W8] using hbelow 1 (by omega)
    · simpa [W8] using hbelow 2 (by omega)
    · simpa [W8] using hbelow 3 (by omega)
    · simpa [W8, ha4] using ha_true
    · simpa [W8] using halpha_up 5 (by omega) (by omega)
    · simpa [W8] using halpha_up 6 (by omega) (by omega)
    · simpa [W8] using halpha_up 7 (by omega) (by omega)
  · right
    have hlen : α.length = W9.length := by rw [hn]; rfl
    refine eq_of_getElem?_of_length hlen ?_
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
      simp [W9] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [W9] using hbelow 0 (by omega)
    · simpa [W9] using hbelow 1 (by omega)
    · simpa [W9] using hbelow 2 (by omega)
    · simpa [W9] using hbelow 3 (by omega)
    · simpa [W9, ha4] using ha_true
    · simpa [W9] using halpha_up 5 (by omega) (by omega)
    · simpa [W9] using halpha_up 6 (by omega) (by omega)
    · simpa [W9] using halpha_up 7 (by omega) (by omega)
    · simpa [W9] using halpha_up 8 (by omega) (by omega)

end UnitDiagonal
