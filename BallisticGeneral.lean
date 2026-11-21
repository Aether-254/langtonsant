import PeriodicWordReduction

/-!
# Ballistic motion from an arbitrary periodic tail

`HighwayFrom.ballisticFrom_of_diagonal` handles only the standard period 104 with a diagonal drift.
Here every periodic tail with positive period (its drift is automatically nonzero) is ballistic,
with explicit constants.  Consequently, for finite initial support,

  `Ballistic s ↔ EventuallyBoundedMemory s ↔ PeriodicTail s`,

and the highway conjecture splits as "every finite orbit has a periodic tail" together with the
finite-word classification `ConsistentWordsAreStandard`.  This is a restatement of the first open
block, not a solution of it.
-/

namespace LangtonsAnt

/-- Squared Euclidean length of the drift, as a natural number. -/
def driftNorm (v : Point) : Nat := v.1.natAbs * v.1.natAbs + v.2.natAbs * v.2.natAbs

/-- `ℓ¹` length of the drift. -/
def driftL1 (v : Point) : Nat := v.1.natAbs + v.2.natAbs

/-- The ant's position eventually repeats up to a translation. -/
def PeriodicTail (s : State) : Prop := exists T P v, 0 < P ∧ HighwayFrom s T P v

theorem linearForm_add (a b : Int) (x y : Point) :
    linearForm a b (x.1 + y.1, x.2 + y.2) = linearForm a b x + linearForm a b y := by
  simp only [linearForm, Int.mul_add]
  omega

theorem linearForm_neg_drift (v : Point) :
    linearForm (-v.1) (-v.2) v = -((driftNorm v : Nat) : Int) := by
  have h1 := Int.natAbs_mul_self' v.1
  have h2 := Int.natAbs_mul_self' v.2
  simp only [linearForm, driftNorm, Int.natCast_add, Int.natCast_mul, Int.neg_mul]
  omega

theorem linearForm_move_le (a b : Int) (x : Point) (d : Direction) :
    linearForm a b (move x d) <= linearForm a b x + ((a.natAbs : Int) + (b.natAbs : Int)) := by
  have ha1 : a <= (a.natAbs : Int) := Int.le_natAbs
  have ha2 : -a <= (a.natAbs : Int) := by simpa using (Int.le_natAbs (a := -a))
  have hb1 : b <= (b.natAbs : Int) := Int.le_natAbs
  have hb2 : -b <= (b.natAbs : Int) := by simpa using (Int.le_natAbs (a := -b))
  cases d <;> simp only [linearForm, move, Int.mul_add, Int.mul_sub, Int.mul_one] <;> omega

theorem driftNorm_pos {v : Point} (hv : v ≠ (0, 0)) : 0 < driftNorm v := by
  unfold driftNorm
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := by
      intro h2
      exact hv (Prod.ext h1 h2)
    have := Nat.mul_pos (Int.natAbs_pos.mpr h2) (Int.natAbs_pos.mpr h2)
    omega
  · have := Nat.mul_pos (Int.natAbs_pos.mpr h1) (Int.natAbs_pos.mpr h1)
    omega

/-- Explicit ballistic constants for any periodic tail: speed `|v|² / P` along `-v`, and
backtracking bound `P * |v|₁ + |v|²`. -/
theorem HighwayFrom.ballisticFrom_of_pos {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (hP : 0 < P) :
    BallisticFrom s T (-v.1) (-v.2) (driftNorm v : Int) (P : Int)
      ((P : Int) * (driftL1 v : Int) + (driftNorm v : Int)) := by
  have hv := h.drift_ne_zero hP
  let f : Nat -> Int := fun t => linearForm (-v.1) (-v.2) (run s t).pos
  let N : Int := (driftNorm v : Int)
  let L : Int := (driftL1 v : Int)
  let g : Nat -> Int := fun t => (P : Int) * f t + N * (t : Int)
  have hN : 0 < N := by
    have := driftNorm_pos hv
    dsimp [N]
    omega
  have hL : 0 <= L := by dsimp [L]; omega
  have hPi : (0 : Int) <= (P : Int) := by omega
  -- One period lowers `f` by `N`, so `g` is `P`-periodic on the tail.
  have hper : forall t, T <= t -> g (t + P) = g t := by
    intro t ht
    have hf : f (t + P) = f t - N := by
      dsimp [f, N]
      rw [(h t ht).1, linearForm_add, linearForm_neg_drift]
      omega
    have hc : N * (P : Int) = (P : Int) * N := Int.mul_comm _ _
    dsimp [g]
    rw [hf, Int.mul_sub, Int.mul_add]
    omega
  have hblocks : forall t, T <= t -> forall k : Nat, g (t + P * k) = g t := by
    intro t ht k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show t + P * (k + 1) = (t + P * k) + P by rw [Nat.mul_succ]; omega,
        hper _ (by omega), ih]
  -- One step raises `g` by at most `K = P * L + N`.
  have hstep : forall t, g (t + 1) <= g t + ((P : Int) * L + N) := by
    intro t
    have hm := linearForm_move_le (-v.1) (-v.2) (run s t).pos
      (turn ((run s t).board (run s t).pos) (run s t).dir)
    change f (t + 1) <= f t + _ at hm
    simp only [Int.natAbs_neg] at hm
    have hm' : f (t + 1) <= f t + L := by dsimp [L, driftL1]; omega
    have hmul := Int.mul_le_mul_of_nonneg_left hm' hPi
    dsimp [g]
    rw [Int.mul_add] at hmul
    rw [Int.mul_add, Int.mul_one]
    omega
  have hrun : forall t r, g (t + r) <= g t + (r : Int) * ((P : Int) * L + N) := by
    intro t r
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep (t + r)
      rw [show t + (r + 1) = t + r + 1 by omega, Int.natCast_add, Int.add_mul, Int.natCast_one,
        Int.one_mul]
      omega
  have hK : 0 <= (P : Int) * L + N := by
    have := Int.mul_nonneg hPi hL
    omega
  refine ⟨hN, by omega, hK, ?_⟩
  intro n m hn hnm
  let k := (m - n) / P
  let r := (m - n) % P
  have hr : r < P := Nat.mod_lt _ hP
  have htime : n + r + P * k = m := by
    have := Nat.div_add_mod (m - n) P
    dsimp [k, r]
    omega
  have h1 : g m = g (n + r) := by rw [← htime, hblocks (n + r) (by omega) k]
  have h2 := hrun n r
  have h3 : (r : Int) * ((P : Int) * L + N) <= (P : Int) * ((P : Int) * L + N) :=
    Int.mul_le_mul_of_nonneg_right (by omega) hK
  have hg : g m <= g n + (P : Int) * ((P : Int) * L + N) := by omega
  dsimp [g, f] at hg
  dsimp [N, L] at hg
  rw [Int.mul_sub]
  omega

theorem HighwayFrom.ballistic {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (hP : 0 < P) : Ballistic s :=
  ⟨T, _, _, _, _, _, h.ballisticFrom_of_pos hP⟩

theorem PeriodicTail.ballistic {s : State} (h : PeriodicTail s) : Ballistic s := by
  obtain ⟨T, P, v, hP, hh⟩ := h
  exact hh.ballistic hP

/-- For finite support the three notions of "eventually regular escape" coincide. -/
theorem ballistic_iff_periodicTail {s : State} (hs : FiniteSupport s.board) :
    Ballistic s ↔ PeriodicTail s := by
  constructor
  · intro h
    obtain ⟨T, P, v, hP, _, hh, _⟩ := h.highway hs
    exact ⟨T, P, v, hP, hh⟩
  · exact PeriodicTail.ballistic

theorem ballistic_iff_eventuallyBoundedMemory {s : State} (hs : FiniteSupport s.board) :
    Ballistic s ↔ EventuallyBoundedMemory s := by
  constructor
  · exact fun h => h.boundedMemory hs
  · intro h
    obtain ⟨T, P, v, hP, _, hh, _⟩ := h.highway
    exact hh.ballistic hP

/-- The conjecture is "every finite orbit eventually repeats up to translation" plus the
finite-word classification.  Both conjuncts remain open. -/
theorem highwayConjecture_iff_periodicTail_and_consistentWordsAreStandard :
    HighwayConjecture ↔
      (forall s : State, FiniteSupport s.board -> PeriodicTail s) ∧ ConsistentWordsAreStandard := by
  rw [highwayConjecture_iff_ballistic_and_consistentWordsAreStandard]
  constructor
  · rintro ⟨hb, hc⟩
    exact ⟨fun s hs => (ballistic_iff_periodicTail hs).mp (hb s hs), hc⟩
  · rintro ⟨hp, hc⟩
    exact ⟨fun s hs => (ballistic_iff_periodicTail hs).mpr (hp s hs), hc⟩

end LangtonsAnt
