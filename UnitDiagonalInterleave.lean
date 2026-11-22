/-
# A purely combinatorial interleaving lemma

Two strictly increasing lists of naturals `p` and `q` whose entries are all below `n`, with the
even numbers below `n` distributed between them (each even number lies in exactly one of the two
lists) and the odd numbers shared (an odd number lies in `p` iff it lies in `q`).
If the third entry of `p` is one more than the second entry of `q`, and the fifth entry of `p` is
one more than the fourth entry of `q`, then either the second entries already agree, or the fifth
entries agree.

The proof only uses elementary properties of strictly increasing lists of naturals.
-/

namespace UnitDiagonal

/-- In a strictly increasing list of naturals, each entry is smaller than the next one. -/
theorem lt_getElem_succ {l : List Nat} (hl : l.Pairwise (· < ·)) {i : Nat}
    (hi : i + 1 < l.length) : l[i] < l[i + 1] := by
  have h1 : i < l.length := by omega
  exact hl.rel_getElem_of_lt h1 hi (by omega)

/-- A strictly increasing list of naturals is monotone in its index. -/
theorem le_getElem_of_le {l : List Nat} (hl : l.Pairwise (· < ·)) {i j : Nat} (hij : i ≤ j)
    (hj : j < l.length) : l[i] ≤ l[j] := by
  rcases Nat.lt_or_eq_of_le hij with hlt | heq
  · have hi : i < l.length := by omega
    exact Nat.le_of_lt (hl.rel_getElem_of_lt hi hj hlt)
  · subst heq
    exact Nat.le_refl _

/-- Above `l[i]`, every entry of a strictly increasing list is at least the next entry `l[i+1]`. -/
theorem le_getElem_succ_of_mem {l : List Nat} (hl : l.Pairwise (· < ·)) {i : Nat}
    (hi : i + 1 < l.length) {x : Nat} (hx : x ∈ l) (hlt : l[i] < x) : l[i + 1] ≤ x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hidx : i + 1 ≤ j := by
    rcases Nat.lt_or_ge j (i + 1) with hlt' | hge
    · have hle : l[j] ≤ l[i] := le_getElem_of_le hl (by omega) (by omega)
      omega
    · exact hge
  exact le_getElem_of_le hl hidx hj

/-- Below `l[i+1]`, every entry of a strictly increasing list is at most `l[i]`. -/
theorem le_getElem_of_mem {l : List Nat} (hl : l.Pairwise (· < ·)) {i : Nat}
    (hi : i + 1 < l.length) {x : Nat} (hx : x ∈ l) (hlt : x < l[i + 1]) : x ≤ l[i] := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hidx : j ≤ i := by
    rcases Nat.lt_or_ge j (i + 1) with hlt' | hge
    · omega
    · have hle : l[i + 1] ≤ l[j] := le_getElem_of_le hl hge hj
      omega
  exact le_getElem_of_le hl hidx (by omega)

/-- Interleaving bridge: if the third entry of `p` is one more than the second entry of `q` and the
fifth entry of `p` is one more than the fourth entry of `q`, then the second entries agree or the
fifth entries agree. -/
theorem interleave_bridge (p q : List Nat) (n : Nat)
    (hp : p.Pairwise (· < ·)) (hq : q.Pairwise (· < ·))
    (hpn : ∀ x ∈ p, x < n) (hqn : ∀ x ∈ q, x < n)
    (hlp : 5 ≤ p.length) (hlq : 5 ≤ q.length)
    (heven : ∀ x, x < n → x % 2 = 0 → (x ∈ p ↔ x ∉ q))
    (hodd : ∀ x, x < n → x % 2 = 1 → (x ∈ p ↔ x ∈ q))
    (h2 : p[2] = q[1] + 1) (h4 : p[4] = q[3] + 1) :
    p[1] = q[1] ∨ p[4] = q[4] := by
  have hp2 : p[2] ∈ p := List.getElem_mem (l := p) (n := 2) (by omega)
  have hp3 : p[3] ∈ p := List.getElem_mem (l := p) (n := 3) (by omega)
  have hp4 : p[4] ∈ p := List.getElem_mem (l := p) (n := 4) (by omega)
  have hq1 : q[1] ∈ q := List.getElem_mem (l := q) (n := 1) (by omega)
  have hq3 : q[3] ∈ q := List.getElem_mem (l := q) (n := 3) (by omega)
  have hp2n : p[2] < n := hpn _ hp2
  have hp3n : p[3] < n := hpn _ hp3
  have hp4n : p[4] < n := hpn _ hp4
  have hq1n : q[1] < n := hqn _ hq1
  have hq3n : q[3] < n := hqn _ hq3
  have hp12 : p[1] < p[2] := lt_getElem_succ hp (by omega)
  have hp23 : p[2] < p[3] := lt_getElem_succ hp (by omega)
  have hp34 : p[3] < p[4] := lt_getElem_succ hp (by omega)
  have hq12 : q[1] < q[2] := lt_getElem_succ hq (by omega)
  have hq34 : q[3] < q[4] := lt_getElem_succ hq (by omega)
  have hq1_lt_p2 : q[1] < p[2] := by omega
  have hq3_lt_p4 : q[3] < p[4] := by omega
  rcases Nat.mod_two_eq_zero_or_one (q[1]) with hq1even | hq1odd
  · -- `q[1]` is even: then `p[2] = q[1] + 1` is odd and is the entry of `q` right after `q[1]`.
    have hp2odd : p[2] % 2 = 1 := by rw [h2]; omega
    have hp2inq : p[2] ∈ q := (hodd _ hp2n hp2odd).mp hp2
    have hq2le : q[2] ≤ p[2] :=
      le_getElem_succ_of_mem hq (i := 1) (by omega) hp2inq (by simpa using hq1_lt_p2)
    have hq2eq : q[2] = p[2] := by omega
    rcases Nat.mod_two_eq_zero_or_one (q[3]) with hq3even | hq3odd
    · -- `q[3]` is even: then `p[4] = q[3] + 1` is odd and is the entry of `q` right after `q[3]`.
      have hp4odd : p[4] % 2 = 1 := by rw [h4]; omega
      have hp4inq : p[4] ∈ q := (hodd _ hp4n hp4odd).mp hp4
      have hq4le : q[4] ≤ p[4] :=
        le_getElem_succ_of_mem hq (i := 3) (by omega) hp4inq (by simpa using hq3_lt_p4)
      exact Or.inr (by omega)
    · -- `q[3]` is odd: then `q[3] = p[3]`, and `p[2] + 1` is an even number strictly between the
      -- odd numbers `p[2] = q[2]` and `p[3] = q[3]`, so it lies in exactly one of `p`, `q`.
      have hq3inp : q[3] ∈ p := (hodd _ hq3n hq3odd).mpr hq3
      have hq3lep3 : q[3] ≤ p[3] :=
        le_getElem_of_mem hp (i := 3) (by omega) hq3inp (by simpa using hq3_lt_p4)
      have hp3eq : p[3] = q[3] := by omega
      have hp3odd : p[3] % 2 = 1 := by rw [hp3eq]; exact hq3odd
      have hxeven : (p[2] + 1) % 2 = 0 := by omega
      have hxlt : p[2] + 1 < p[3] := by omega
      have hxn : p[2] + 1 < n := by omega
      by_cases hxp : p[2] + 1 ∈ p
      · have hle : p[3] ≤ p[2] + 1 :=
          le_getElem_succ_of_mem hp (i := 2) (by omega) hxp (by omega)
        omega
      · by_cases hxq : p[2] + 1 ∈ q
        · have hle : q[3] ≤ p[2] + 1 :=
            le_getElem_succ_of_mem hq (i := 2) (by omega) hxq (by omega)
          omega
        · exact absurd ((heven _ hxn hxeven).mpr hxq) hxp
  · -- `q[1]` is odd: it is an entry of `p` just below `p[2]`, hence it equals `p[1]`.
    have hq1inp : q[1] ∈ p := (hodd _ hq1n hq1odd).mpr hq1
    have hq1lep1 : q[1] ≤ p[1] :=
      le_getElem_of_mem hp (i := 1) (by omega) hq1inp (by simpa using hq1_lt_p2)
    exact Or.inl (by omega)

end UnitDiagonal
