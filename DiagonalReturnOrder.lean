import DiagonalMultipleLanes
import PortBridge

/-!
# Order constraints on zero-displacement upper returns

This file formalizes rounds 15 and 16--17 of
`research/persist-B-diagonal-m3-2026-11-22.md`.

`ZeroReturn a e j i` records the necessary rank equation `p[i] = q[j] + 1`,
where `p = trueIdx a` and `q = trueIdx (UnitDiagonal.beta a e)`.  It does
not assert that an arbitrary pair of ports is realized by a physical path.
`UpperReturn` supplies that geometric witness, including the actual lifted
position and strict separation of all intermediate points from its layer.

The round-12 first-incidence advance is already proved in
`UnitDiagonal.first_index_corollary`; it is reused here, not reproved.
Neither minimal read period nor any bound on table length is assumed.
The cycle theorem permits fixed points: it excludes nonconstant cycles only.
-/

namespace LangtonsAnt.DiagonalReturnOrder

open DiagonalMultipleLanes

/-- The rank equation forced by a physical first return from outgoing port
`j` to incoming port `i`.  Port numbers are distinct from visit ranks. -/
def ZeroReturn (a : List Bool) (e : Bool) (j i : Nat) : Prop :=
  ∃ k, (UnitDiagonal.trueIdx (UnitDiagonal.beta a e))[j]? = some k ∧
    (UnitDiagonal.trueIdx a)[i]? = some (k + 1)

private theorem lookup_lt_iff {l : List Nat} (hs : l.Pairwise (· < ·))
    {i j a b : Nat} (hi : l[i]? = some a) (hj : l[j]? = some b) :
    i < j ↔ a < b := by
  constructor
  · exact fun h => UnitDiagonal.lt_of_pairwise hs h hi hj
  · intro hab
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact h
    · subst j
      rw [hi] at hj
      have := Option.some.inj hj
      omega
    · have := UnitDiagonal.lt_of_pairwise hs h hj hi
      omega

private theorem lookup_eq_iff {l : List Nat} (hs : l.Pairwise (· < ·))
    {i j a b : Nat} (hi : l[i]? = some a) (hj : l[j]? = some b) :
    i = j ↔ a = b := by
  have hlt := lookup_lt_iff hs hi hj
  have hgt := lookup_lt_iff hs hj hi
  omega

/-- Rounds 16--17: zero-return pairs form a strictly increasing partial
map.  The equivalence also gives order reflection. -/
theorem zeroReturn_strict_order {a : List Bool} {e : Bool} {j i j' i' : Nat}
    (h : ZeroReturn a e j i) (h' : ZeroReturn a e j' i') :
    j < j' ↔ i < i' := by
  obtain ⟨k, hq, hp⟩ := h
  obtain ⟨k', hq', hp'⟩ := h'
  have hqord := lookup_lt_iff (UnitDiagonal.pairwise_trueIdx _) hq hq'
  have hpord := lookup_lt_iff (UnitDiagonal.pairwise_trueIdx _) hp hp'
  omega

/-- A departure port has at most one zero-return arrival, and conversely. -/
theorem zeroReturn_port_eq_iff {a : List Bool} {e : Bool} {j i j' i' : Nat}
    (h : ZeroReturn a e j i) (h' : ZeroReturn a e j' i') :
    j = j' ↔ i = i' := by
  have hlt := zeroReturn_strict_order h h'
  have hgt := zeroReturn_strict_order h' h
  omega

/-- Round 15: after `j -> 0`, a zero return from the next departure port
can only end at incoming port `1`. -/
theorem zeroReturn_adjacent_first {a : List Bool} {e : Bool} {j i : Nat}
    (hfirst : ZeroReturn a e j 0) (hnext : ZeroReturn a e (j + 1) i) :
    i = 1 := by
  obtain ⟨k, hq, hp⟩ := hfirst
  obtain ⟨k', hq', hp'⟩ := hnext
  have hbridge := (UnitDiagonal.first_index_corollary e hp hq).2.2
  have hk : k' = k + 1 := Option.some.inj (hq'.symm.trans hbridge)
  subst k'
  have hmem : k + 1 + 1 ∈ UnitDiagonal.trueIdx a :=
    List.mem_iff_getElem?.mpr ⟨i, hp'⟩
  have hp1 := UnitDiagonal.getElem?_succ_of_mem
    (UnitDiagonal.pairwise_trueIdx a) hp hmem
  exact (lookup_eq_iff (UnitDiagonal.pairwise_trueIdx a) hp' hp1).mpr rfl

/-- The forbidden adjacent-return pattern, with its exact exceptional
arrival index exposed rather than silently excluded. -/
theorem zeroReturn_adjacent_forbidden {a : List Bool} {e : Bool} {j i : Nat}
    (hfirst : ZeroReturn a e j 0) (hi : i ≠ 1) :
    ¬ ZeroReturn a e (j + 1) i := by
  intro hnext
  exact hi (zeroReturn_adjacent_first hfirst hnext)

private theorem chain_endpoint {R : Nat → Nat → Prop}
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (f : Nat → Nat) {n : Nat} (hn : 0 < n)
    (hstep : ∀ k, k < n → R (f k) (f (k + 1))) : R (f 0) (f n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      exact hstep 0 (by omega)
    · exact htrans (ih (by omega) (fun k hk => hstep k (by omega)))
        (hstep n (by omega))

/-- Round 17: a finite closed chain of zero-return port numbers is
constant.  In particular, fixed points are allowed, but longer cycles
with distinct vertices are impossible. -/
theorem zeroReturn_cycle_constant {a : List Bool} {e : Bool}
    (f : Nat → Nat) {n : Nat} (hn : 0 < n) (hclose : f n = f 0)
    (hedge : ∀ k, k < n → ZeroReturn a e (f k) (f (k + 1))) :
    ∀ k, k ≤ n → f k = f 0 := by
  have hfixed : f 1 = f 0 := by
    rcases Nat.lt_trichotomy (f 0) (f 1) with h | h | h
    · have hs : ∀ k, k < n → f k < f (k + 1) := by
        intro k hk
        induction k with
        | zero => exact h
        | succ k ih =>
          exact (zeroReturn_strict_order (hedge k (by omega))
            (hedge (k + 1) hk)).mp (ih (by omega))
      have hc := chain_endpoint (R := (· < ·))
        (fun hxy hyz => Nat.lt_trans hxy hyz) f hn hs
      omega
    · exact h.symm
    · have hs : ∀ k, k < n → f (k + 1) < f k := by
        intro k hk
        induction k with
        | zero => exact h
        | succ k ih =>
          exact (zeroReturn_strict_order (hedge (k + 1) hk)
            (hedge k (by omega))).mp (ih (by omega))
      have hc := chain_endpoint (R := fun x y => y < x)
        (fun hxy hyz => Nat.lt_trans hyz hxy) f hn hs
      omega
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := (zeroReturn_port_eq_iff (hedge k (by omega)) (hedge 0 hn)).mp
      (ih (by omega))
    exact hh.trans hfixed

/-- A physical zero-displacement excursion above the cell at depth `n`
and horizontal coordinate `r`, with the indicated ordered ports.
`period` in the continuous path records crossings of the chosen word period. -/
def UpperReturn (m P : Nat) (w : Nat → Bool) (n : Nat) (r : Int)
    (j i : Nat) : Prop :=
  ∃ len, ∃ p : ContinuousPhasePath P len,
    0 < len ∧
    p.pos w 0 = laneCell (topLayer P w - (n : Int)) r ∧
    p.pos w len = p.pos w 0 ∧
    (∀ k, 0 < k → k < len → layer (p.pos w 0) < layer (p.pos w k)) ∧
    (UnitDiagonal.trueIdx (laneBeta m P w (topLayer P w - (n : Int)) r))[j]? =
      some (Drift.stableRank P w (p.phase 0)) ∧
    (UnitDiagonal.trueIdx (laneAlpha m P w (topLayer P w - (n : Int)) r))[i]? =
      some (Drift.stableRank P w (p.phase len))

/-- The geometric-to-list interface: strict upper-layer separation proves
physical first return, even when the excursion crosses a period boundary. -/
theorem upperReturn_zeroReturn {m P n j i : Nat} {w : Nat → Bool} {r : Int}
    (hc : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (h : UpperReturn m P w n r j i) :
    ZeroReturn (laneAlpha m P w (topLayer P w - (n : Int)) r)
      (decide (n % 2 = 1)) j i := by
  obtain ⟨len, p, hlen, _, hret, habove, hq, hp⟩ := h
  have hrank := Drift.path_firstReturn_rank p hd (diagDrift_ne_zero hm) hlen hret
    (by
      intro k hk hkl he
      have hl := habove k hk hkl
      rw [he] at hl
      omega)
  refine ⟨Drift.stableRank P w (p.phase 0), ?_, ?_⟩
  · simpa only [laneBeta_eq hc hm hd n r] using hq
  · simpa only [hrank] using hp

/-- Rounds 16--17 on actual lifted paths at one fixed physical boundary cell. -/
theorem upperReturn_strict_order {m P n j i j' i' : Nat} {w : Nat → Bool} {r : Int}
    (hc : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (h : UpperReturn m P w n r j i) (h' : UpperReturn m P w n r j' i') :
    j < j' ↔ i < i' :=
  zeroReturn_strict_order (upperReturn_zeroReturn hc hm hd h)
    (upperReturn_zeroReturn hc hm hd h')

/-- Round 15 on actual lifted paths; no completion of the lower layers is
needed to rule out any second arrival other than port `1`. -/
theorem upperReturn_adjacent_first {m P n j i : Nat} {w : Nat → Bool} {r : Int}
    (hc : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (hfirst : UpperReturn m P w n r j 0)
    (hnext : UpperReturn m P w n r (j + 1) i) : i = 1 :=
  zeroReturn_adjacent_first (upperReturn_zeroReturn hc hm hd hfirst)
    (upperReturn_zeroReturn hc hm hd hnext)

/-- The physical return relation has no nonconstant finite port-number cycle. -/
theorem upperReturn_cycle_constant {m P n len : Nat} {w : Nat → Bool} {r : Int}
    (hc : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (f : Nat → Nat) (hlen : 0 < len) (hclose : f len = f 0)
    (hedge : ∀ k, k < len → UpperReturn m P w n r (f k) (f (k + 1))) :
    ∀ k, k ≤ len → f k = f 0 :=
  zeroReturn_cycle_constant f hlen hclose
    (fun k hk => upperReturn_zeroReturn hc hm hd (hedge k hk))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The standard southeast highway has arrival ranks `[2, 3, 4, 5]`
at depth eight in the odd lane.  This finite certificate is kernel-reduced. -/
theorem stdHighwaySE_depth8_alpha :
    laneAlpha 2 104 TwoCellDiagonal.stdHighwaySE
      (topLayer 104 TwoCellDiagonal.stdHighwaySE - ((8 : Nat) : Int)) 1 =
      [false, false, true, true, true, true] := by
  rw [TwoCellDiagonal.stdHighwaySE_topLayer]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Phases `1 -> 9`: an eight-step upper return to physical cell `(1, 0)`.
It realizes the allowed port-number fixed point `0 -> 0`. -/
theorem stdHighwaySE_return_zero :
    UpperReturn 2 104 TwoCellDiagonal.stdHighwaySE 8 1 0 0 := by
  let p := ContinuousPhasePath.ofStart (by decide : 0 < 104) 1 8
  refine ⟨8, p, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [TwoCellDiagonal.stdHighwaySE_topLayer]
    decide +kernel
  · decide +kernel
  · have h : ∀ k : Fin 8, 0 < k.val →
        layer (p.pos TwoCellDiagonal.stdHighwaySE 0) <
          layer (p.pos TwoCellDiagonal.stdHighwaySE k.val) := by decide +kernel
    intro k hk hkl
    exact h ⟨k, hkl⟩ hk
  · rw [laneBeta_eq TwoCellDiagonal.stdHighwaySE_consistent (by decide)
        TwoCellDiagonal.stdHighwaySE_drift, stdHighwaySE_depth8_alpha]
    decide +kernel
  · rw [stdHighwaySE_depth8_alpha]
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Phases `9 -> 85`: the next upper return at the same physical cell,
of length 76, realizes `1 -> 1`. -/
theorem stdHighwaySE_return_one :
    UpperReturn 2 104 TwoCellDiagonal.stdHighwaySE 8 1 1 1 := by
  let p := ContinuousPhasePath.ofStart (by decide : 0 < 104) 9 76
  refine ⟨76, p, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [TwoCellDiagonal.stdHighwaySE_topLayer]
    decide +kernel
  · decide +kernel
  · have h : ∀ k : Fin 76, 0 < k.val →
        layer (p.pos TwoCellDiagonal.stdHighwaySE 0) <
          layer (p.pos TwoCellDiagonal.stdHighwaySE k.val) := by decide +kernel
    intro k hk hkl
    exact h ⟨k, hkl⟩ hk
  · rw [laneBeta_eq TwoCellDiagonal.stdHighwaySE_consistent (by decide)
        TwoCellDiagonal.stdHighwaySE_drift, stdHighwaySE_depth8_alpha]
    decide +kernel
  · rw [stdHighwaySE_depth8_alpha]
    decide +kernel

/-- Both adjacent-return hypotheses occur in a genuine consistent word;
the arrival of the second one is forced to be port `1`. -/
theorem stdHighwaySE_nonvacuity :
    ConsistentWord 104 TwoCellDiagonal.stdHighwaySE ∧
    wordDrift 104 TwoCellDiagonal.stdHighwaySE = (2, -2) ∧
    UpperReturn 2 104 TwoCellDiagonal.stdHighwaySE 8 1 0 0 ∧
    UpperReturn 2 104 TwoCellDiagonal.stdHighwaySE 8 1 1 1 ∧
    (∀ i, UpperReturn 2 104 TwoCellDiagonal.stdHighwaySE 8 1 1 i → i = 1) := by
  refine ⟨TwoCellDiagonal.stdHighwaySE_consistent, TwoCellDiagonal.stdHighwaySE_drift,
    stdHighwaySE_return_zero, stdHighwaySE_return_one, ?_⟩
  intro i hi
  exact upperReturn_adjacent_first TwoCellDiagonal.stdHighwaySE_consistent (by decide)
    TwoCellDiagonal.stdHighwaySE_drift stdHighwaySE_return_zero hi

end LangtonsAnt.DiagonalReturnOrder
