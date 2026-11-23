import BlackCountBound2

/-!
# Fixed-direction progress budget

The paper's E_W(N) is `missCount s W W (N - W)`, including the empty
interval when N < W. We also bound the stronger count starting at zero.
The projection is fixed in time; its one-step Lipschitz condition is explicit.
No disjointness of physical black lifetimes is assumed.

Proof audit: every repeated miss has an earlier equal position outside the
window. Any such visit suffices, so selecting the last visit or proving its
white birth color is unnecessary for this upper bound. The two endpoint
remainders give the projection bound; compensated progress then supplies the
deficit interval. `backward_charging` charges from the right using strong
induction, allowing arbitrary overlaps. First black visits inject into the
initial black set, whose exact size is `(unique s.black).length` even for a
list representation with duplicates.

`directional_budget_floor` and `directional_budget_zero` count [0,N).
`directional_budget` uses exactly the paper's [W,N). The sublinearity
corollary uses reciprocal integer precisions, an epsilon-N formulation that
needs no real-number library. No claim is made that every finite initial
state admits a direction and scale with sublinear deficit.
-/

namespace LangtonsAnt.DirectionalBudget

open BlackCountBound

def progressDefect (h : Nat -> Int) (k : Nat) : Nat :=
  (1 - (h (k + 1) - h k)).toNat

def totalDefect (h : Nat -> Int) : Nat -> Nat
  | 0 => 0
  | k + 1 => totalDefect h k + progressDefect h k

theorem totalDefect_mono (h : Nat -> Int) {a b : Nat} (hab : a <= b) :
    totalDefect h a <= totalDefect h b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp
  | succ k ih =>
      change totalDefect h a <= totalDefect h (a + k) + progressDefect h (a + k)
      omega

theorem compensated_interval (h : Nat -> Int) (a k : Nat) :
    (k : Int) <= h (a + k) - h a +
      (totalDefect h (a + k) : Int) - (totalDefect h a : Int) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs : 1 <= h (a + k + 1) - h (a + k) + (progressDefect h (a + k) : Int) := by
        unfold progressDefect
        omega
      change ((k + 1 : Nat) : Int) <= h (a + k + 1) - h a +
        ((totalDefect h (a + k) + progressDefect h (a + k) : Nat) : Int) - _
      omega

theorem long_return_deficit (h : Nat -> Int) {j k L : Nat}
    (hjk : j <= k) (hlong : 4 * L <= k - j)
    (hnear : h k - h j <= 2 * (L : Int)) :
    k - j <= 2 * (totalDefect h k - totalDefect h j) := by
  have hc := compensated_interval h j (k - j)
  have hm := totalDefect_mono h hjk
  rw [Nat.add_sub_of_le hjk] at hc
  omega

/-- Weighted right-endpoint charging, with arbitrary overlapping witnesses. -/
theorem backward_charging (F D : Nat -> Nat) (L : Nat)
    (hzero : F 0 = 0)
    (hmono : forall a b, a <= b -> D a <= D b)
    (hinc : forall j k, j <= k -> F k <= F j + L * (k - j))
    (hw : forall k, 0 < k -> F (k - 1) < F k ->
      exists j, j < k ∧ k - j <= 2 * (D k - D j))
    (N : Nat) : F N <= L * (2 * D N) := by
  induction N using Nat.strongRecOn with
  | ind N ih =>
      cases N with
      | zero => simp [hzero]
      | succ n =>
          by_cases hf : F n < F (n + 1)
          · obtain ⟨j, hj, hb⟩ := hw (n + 1) (by omega) (by simpa using hf)
            have hp := ih j hj
            have hc := hinc j (n + 1) (by omega)
            have hd := hmono j (n + 1) (by omega)
            have hb' := Nat.mul_le_mul_left L hb
            have hd' := Nat.mul_le_mul_left L (Nat.mul_le_mul_left 2 hd)
            simp only [Nat.mul_sub] at hb' hd' hp hc
            omega
          · have hp := ih n (by omega)
            have hd := Nat.mul_le_mul_left L
              (Nat.mul_le_mul_left 2 (hmono n (n + 1) (by omega)))
            omega

def UnitProjection (s : State) (f : Point -> Int) : Prop :=
  forall n, -1 <= f (run s (n + 1)).pos - f (run s n).pos ∧
    f (run s (n + 1)).pos - f (run s n).pos <= 1

def heights (s : State) (f : Point -> Int) (L k : Nat) : Int :=
  f (run s (k * L)).pos

def window (L : Nat) : Nat := L * (4 * L + 2)

def ceilBlocks (N L : Nat) : Nat := (N + L - 1) / L

theorem projection_displacement {s : State} {f : Point -> Int}
    (hf : UnitProjection s f) (a k : Nat) :
    -(k : Int) <= f (run s (a + k)).pos - f (run s a).pos ∧
    f (run s (a + k)).pos - f (run s a).pos <= k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hf (a + k)
      change -(↑(k + 1) : Int) <= f (run s (a + k + 1)).pos - _ ∧
        f (run s (a + k + 1)).pos - _ <= ↑(k + 1)
      omega

theorem long_gap_block_indices {L j k rb re : Nat}
    (hrb : rb < L) (hre : re < L)
    (hgap : j * L + rb + window L < k * L + re) :
    j < k ∧ 4 * L <= k - j := by
  have hs : j + 4 * L < k := by
    by_cases hn : j + 4 * L < k
    · exact hn
    · have hm := Nat.mul_le_mul_right L (show k <= j + 4 * L by omega)
      have hdist : window L = (4 * L) * L + 2 * L := by
        simp only [window, Nat.mul_add, Nat.mul_comm L (4 * L), Nat.mul_comm L 2]
      rw [Nat.add_mul] at hm
      rw [hdist] at hgap
      omega
  omega

def count (g : Nat -> Bool) : Nat -> Nat
  | 0 => 0
  | n + 1 => count g n + if g n then 1 else 0

theorem count_interval (g : Nat -> Bool) (a k : Nat) :
    count g a <= count g (a + k) ∧ count g (a + k) <= count g a + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      change count g a <= count g (a + k) + (if g (a + k) then 1 else 0) ∧
        count g (a + k) + (if g (a + k) then 1 else 0) <= count g a + (k + 1)
      split <;> omega

theorem count_mono (g : Nat -> Bool) {a b : Nat} (hab : a <= b) :
    count g a <= count g b := by
  have h := (count_interval g a (b - a)).1
  simpa only [Nat.add_sub_of_le hab] using h

theorem count_growth_witness (g : Nat -> Bool) (a k : Nat)
    (hg : count g a < count g (a + k)) :
    exists n, a <= n ∧ n < a + k ∧ g n = true := by
  induction k with
  | zero => simp at hg
  | succ k ih =>
      by_cases hn : g (a + k) = true
      · exact ⟨a + k, by omega, by omega, hn⟩
      · have he : count g (a + (k + 1)) = count g (a + k) := by
          simp [count, hn]
        rw [he] at hg
        obtain ⟨n, ha, hb, hn⟩ := ih hg
        exact ⟨n, ha, by omega, hn⟩

theorem count_eq_filter (g : Nat -> Bool) (N : Nat) :
    count g N = ((List.range N).filter g).length := by
  induction N with
  | zero => rfl
  | succ N ih => cases hn : g N <;> simp [count, List.range_succ, ih, hn]

def firstBlack (s : State) (n : Nat) : Bool :=
  readColor s n && ((List.range n).all (fun b => decide ((run s b).pos ≠ (run s n).pos)))

theorem firstBlack_iff (s : State) (n : Nat) :
    firstBlack s n = true ↔ readColor s n = true ∧
      forall b, b < n -> (run s b).pos ≠ (run s n).pos := by
  simp [firstBlack, List.all_eq_true]

def repeatedMiss (s : State) (W n : Nat) : Bool :=
  cacheMissBit s W n && !firstBlack s n

theorem repeatedMiss_iff (s : State) (W n : Nat) :
    repeatedMiss s W n = true ↔ cacheMissBit s W n = true ∧
      exists b, b < n ∧ (run s b).pos = (run s n).pos := by
  rw [repeatedMiss, Bool.and_eq_true, Bool.not_eq_true']
  have hc := (cacheMissBitC_iff s W n)
  constructor
  · rintro ⟨hm, hb⟩
    refine ⟨hm, ?_⟩
    have hr := (hc.mp hm).1
    have hn : ¬firstBlack s n = true := by simp [hb]
    apply Classical.byContradiction
    intro hno
    apply hn
    exact (firstBlack_iff s n).mpr ⟨hr, fun b hb hp => hno ⟨b, hb, hp⟩⟩
  · rintro ⟨hm, b, hb, hp⟩
    refine ⟨hm, ?_⟩
    cases he : firstBlack s n with
    | false => rfl
    | true => exact False.elim (((firstBlack_iff s n).mp he).2 b hb hp)

theorem board_before_first (s : State) (p : Point) (n : Nat)
    (h : forall b, b < n -> (run s b).pos ≠ p) :
    (run s n).board p = s.board p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change flip (run s n).board (run s n).pos p = _
      rw [flip_other _ (Ne.symm (h n (by omega)))]
      exact ih (fun b hb => h b (by omega))

theorem firstBlack_count_le (s : FiniteState) (N : Nat) :
    count (firstBlack s.toState) N <= (unique s.black).length := by
  let ts := (List.range N).filter (firstBlack s.toState)
  let ps := ts.map (fun n => (run s.toState n).pos)
  have hmem : forall n, n ∈ ts -> firstBlack s.toState n = true := by
    intro n hn; exact (List.mem_filter.mp hn).2
  have hnd : ps.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.nodup_range.filter (firstBlack s.toState))
    intro a b ha hb hab hp
    have hfa := ((firstBlack_iff _ _).mp (hmem a ha)).2
    have hfb := ((firstBlack_iff _ _).mp (hmem b hb)).2
    by_cases hlt : a < b
    · exact hfb a hlt hp
    · exact hfa b (by omega) hp.symm
  have hsub : ps ⊆ unique s.black := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hc, ha⟩ := (firstBlack_iff _ _).mp (hmem n hn)
    have he := board_before_first s.toState (run s.toState n).pos n ha
    change (run s.toState n).board (run s.toState n).pos = true at hc
    rw [he] at hc
    exact (mem_unique _ _).mpr (of_decide_eq_true hc)
  have hb := hnd.length_le_of_subset hsub
  simpa only [ps, List.length_map, ts, count_eq_filter] using hb

theorem repeatedMiss_deficit {s : State} {f : Point -> Int}
    (hf : UnitProjection s f) {L : Nat} (hL : 0 < L) {e : Nat}
    (he : repeatedMiss s (window L) e = true) :
    exists j, j < e / L ∧ e / L - j <=
      2 * (totalDefect (heights s f L) (e / L) - totalDefect (heights s f L) j) := by
  obtain ⟨hm, b, hb, hp⟩ := (repeatedMiss_iff _ _ _).mp he
  have hgap : b + window L < e := by
    have hno := ((cacheMissBitC_iff _ _ _).mp hm).2
    by_cases hn : e <= b + window L
    · exact False.elim (hno ⟨b, hb, hn, hp⟩)
    · omega
  have hbd := Nat.div_add_mod' b L
  have hed := Nat.div_add_mod' e L
  have hbr := Nat.mod_lt b hL
  have her := Nat.mod_lt e hL
  have hi := long_gap_block_indices (j := b / L) (k := e / L) hbr her
    (by simpa only [hbd, hed] using hgap)
  have hpb := projection_displacement hf (b / L * L) (b % L)
  have hpe := projection_displacement hf (e / L * L) (e % L)
  rw [hbd, hp] at hpb
  rw [hed] at hpe
  have hnear : heights s f L (e / L) - heights s f L (b / L) <= 2 * (L : Int) := by
    unfold heights
    omega
  exact ⟨b / L, hi.1, long_return_deficit _ (by omega) hi.2 hnear⟩

theorem repeatedMiss_count_blocks {s : State} {f : Point -> Int}
    (hf : UnitProjection s f) {L : Nat} (hL : 0 < L) (K : Nat) :
    count (repeatedMiss s (window L)) ((K + 1) * L) <=
      L * (2 * totalDefect (heights s f L) K) := by
  let g := repeatedMiss s (window L)
  apply backward_charging (fun k => count g ((k + 1) * L)) (totalDefect (heights s f L)) L
  · change count g (1 * L) = 0
    rw [Nat.one_mul]
    by_cases hz : count g L = 0
    · exact hz
    · have hpos : count g 0 < count g (0 + L) := by simp [count]; omega
      obtain ⟨n, _, hn, hg⟩ := count_growth_witness g 0 L hpos
      obtain ⟨j, hj, _⟩ := repeatedMiss_deficit hf hL hg
      rw [Nat.div_eq_of_lt (by omega : n < L)] at hj
      omega
  · intro a b hab; exact totalDefect_mono _ hab
  · intro j k hjk
    have he : (j + 1) * L + L * (k - j) = (k + 1) * L := by
      rw [Nat.mul_comm L (k - j), ← Nat.add_mul]
      congr 1
      omega
    have hc := (count_interval g ((j + 1) * L) (L * (k - j))).2
    simpa only [he] using hc
  · intro k hk hg
    have he : (k - 1 + 1) * L = k * L := by congr 1; omega
    rw [he] at hg
    have he' : k * L + L = (k + 1) * L := by simp [Nat.add_mul]
    obtain ⟨n, hn0, hn1, hgn⟩ := count_growth_witness g (k * L) L (by simpa only [he'] using hg)
    have hnk : n / L = k := Nat.div_eq_of_lt_le hn0 (by simpa only [he'] using hn1)
    simpa only [hnk] using repeatedMiss_deficit hf hL hgn

theorem repeatedMiss_count_le {s : State} {f : Point -> Int}
    (hf : UnitProjection s f) {L : Nat} (hL : 0 < L) (N : Nat) :
    count (repeatedMiss s (window L)) N <=
      L * (2 * totalDefect (heights s f L) (N / L)) := by
  have hd := Nat.div_add_mod' N L
  have hm := Nat.mod_lt N hL
  have hn : N <= (N / L + 1) * L := by rw [Nat.add_mul]; simp only [Nat.one_mul]; omega
  exact Nat.le_trans (count_mono _ hn) (repeatedMiss_count_blocks hf hL (N / L))

theorem miss_count_split (s : State) (W N : Nat) :
    count (cacheMissBit s W) N <= count (firstBlack s) N + count (repeatedMiss s W) N := by
  induction N with
  | zero => simp [count]
  | succ N ih =>
      cases hm : cacheMissBit s W N <;> cases hb : firstBlack s N <;>
        simp only [count, repeatedMiss, hm, hb, Bool.not_false, Bool.not_true,
          Bool.and_true, Bool.and_false,
          Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem count_eq_sumFrom (g : Nat -> Bool) (N : Nat) :
    (count g N : Int) = sumFrom (fun n => bitInt (g n)) 0 N := by
  induction N with
  | zero => rfl
  | succ N ih => cases h : g N <;> simp [count, sumFrom, bitInt, h, ih]

theorem directional_budget_count_floor (s : FiniteState) (f : Point -> Int)
    (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L) (N : Nat) :
    count (cacheMissBit s.toState (window L)) N <= (unique s.black).length +
      2 * L * totalDefect (heights s.toState f L) (N / L) := by
  have hs := miss_count_split s.toState (window L) N
  have hi := firstBlack_count_le s N
  have hr := repeatedMiss_count_le hf hL N
  rw [Nat.mul_left_comm, ← Nat.mul_assoc] at hr
  omega

/-- All misses in [0,N), with the slightly stronger floor-block budget. -/
theorem directional_budget_floor (s : FiniteState) (f : Point -> Int)
    (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L) (N : Nat) :
    missCount s.toState (window L) 0 N <= (unique s.black).length +
      2 * (L : Int) * (totalDefect (heights s.toState f L) (N / L) : Int) := by
  have ht := directional_budget_count_floor s f hf hL N
  have hc : (count (cacheMissBit s.toState (window L)) N : Int) <=
      ((unique s.black).length + 2 * L * totalDefect (heights s.toState f L) (N / L) : Nat) := by
    exact_mod_cast ht
  rw [count_eq_sumFrom] at hc
  simpa [missCount, Int.mul_left_comm, Int.mul_assoc] using hc

theorem floor_le_ceil {L : Nat} (hL : 0 < L) (N : Nat) : N / L <= ceilBlocks N L := by
  apply Nat.div_le_div_right
  omega

/-- The paper budget, also valid for early times: every miss in [0,N) is counted. -/
theorem directional_budget_zero (s : FiniteState) (f : Point -> Int)
    (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L) (N : Nat) :
    missCount s.toState (window L) 0 N <= (unique s.black).length +
      2 * (L : Int) * (totalDefect (heights s.toState f L) (ceilBlocks N L) : Int) := by
  have hb := directional_budget_floor s f hf hL N
  have hd := totalDefect_mono (heights s.toState f L) (floor_le_ceil hL N)
  have hm := Nat.mul_le_mul_left (2 * L) hd
  have hm' : (2 * (L : Int)) * (totalDefect (heights s.toState f L) (N / L) : Int) <=
      (2 * (L : Int)) * (totalDefect (heights s.toState f L) (ceilBlocks N L) : Int) := by
    exact_mod_cast hm
  omega

theorem missCount_nonneg (s : State) (W a N : Nat) : 0 <= missCount s W a N := by
  induction N with
  | zero => exact Int.le_refl 0
  | succ N ih =>
      change 0 <= missCount s W a N + bitInt (cacheMissBit s W (a + N))
      unfold bitInt
      split <;> omega

theorem missCount_suffix_le (s : State) (W N : Nat) :
    missCount s W W (N - W) <= missCount s W 0 N := by
  by_cases hW : W <= N
  · have he := sumFrom_add (fun n => bitInt (cacheMissBit s W n)) 0 W (N - W)
    rw [Nat.add_sub_of_le hW, Nat.zero_add] at he
    change missCount s W 0 N = missCount s W 0 W + missCount s W W (N - W) at he
    have hn := missCount_nonneg s W 0 W
    omega
  · have he : N - W = 0 := by omega
    rw [he]
    exact missCount_nonneg s W 0 N

/-- C9 exactly as defined in the paper: W <= n < N, empty if N < W. -/
theorem directional_budget (s : FiniteState) (f : Point -> Int)
    (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L) (N : Nat) :
    missCount s.toState (window L) (window L) (N - window L) <=
      (unique s.black).length +
      2 * (L : Int) * (totalDefect (heights s.toState f L) (ceilBlocks N L) : Int) :=
  Int.le_trans (missCount_suffix_le _ _ _) (directional_budget_zero s f hf hL N)

/-- For a duplicate-free representation the initial-set size is s.black.length. -/
theorem directional_budget_nodup (s : FiniteState) (hs : s.black.Nodup)
    (f : Point -> Int) (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L) (N : Nat) :
    missCount s.toState (window L) (window L) (N - window L) <= s.black.length +
      2 * (L : Int) * (totalDefect (heights s.toState f L) (ceilBlocks N L) : Int) := by
  have hp : (unique s.black).Perm s.black :=
    (List.perm_ext_iff_of_nodup (nodup_unique s.black) hs).mpr (fun p => mem_unique p s.black)
  simpa only [hp.length_eq] using directional_budget s f hf hL N

/-- Reciprocal-epsilon formulation of a(N)=o(N), using epsilon=1/q.
These precisions are cofinal among positive real epsilons, without using reals. -/
def Sublinear (a : Nat -> Nat) : Prop :=
  forall q, 0 < q -> exists N0, forall N, N0 <= N -> q * a N <= N

/-- The signed-count version also states nonnegativity on the eventual tail. -/
def SublinearInt (a : Nat -> Int) : Prop :=
  forall q : Nat, 0 < q -> exists N0, forall N, N0 <= N ->
    0 <= a N ∧ (q : Int) * a N <= (N : Int)

theorem sublinear_of_block_budget (E D : Nat -> Nat) (B C L : Nat)
    (hC : 0 < C) (hL : 0 < L)
    (hb : forall N, E N <= B + C * D (N / L))
    (hd : Sublinear D) : Sublinear E := by
  intro q hq
  obtain ⟨K0, hK⟩ := hd (2 * (q * C)) (Nat.mul_pos (by decide) (Nat.mul_pos hq hC))
  refine ⟨max (K0 * L) (2 * (q * B)), ?_⟩
  intro N hN
  have hKN : K0 <= N / L := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hD := Nat.le_trans (hK (N / L) hKN) (Nat.div_le_self N L)
  have hD' : 2 * (q * (C * D (N / L))) <= N := by
    simpa only [Nat.mul_assoc] using hD
  have hE := Nat.mul_le_mul_left q (hb N)
  rw [Nat.mul_add] at hE
  omega

/-- Fixed direction and fixed scale: sublinear deficit implies sublinear misses,
even when the misses are counted from time zero. -/
theorem sublinear_zero_of_defect (s : FiniteState) (f : Point -> Int)
    (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L)
    (hd : Sublinear (totalDefect (heights s.toState f L))) :
    SublinearInt (fun N => missCount s.toState (window L) 0 N) := by
  have hc := sublinear_of_block_budget (count (cacheMissBit s.toState (window L)))
    (totalDefect (heights s.toState f L)) (unique s.black).length (2 * L) L
    (by omega) hL (directional_budget_count_floor s f hf hL) hd
  intro q hq
  obtain ⟨N0, hN⟩ := hc q hq
  refine ⟨N0, fun N hn => ⟨missCount_nonneg _ _ _ _, ?_⟩⟩
  have h := hN N hn
  have hi : (q : Int) * (count (cacheMissBit s.toState (window L)) N : Int) <= N := by
    exact_mod_cast h
  simpa only [count_eq_sumFrom, missCount] using hi

/-- The paper's exact C-M conclusion, conditional on the directional hypothesis. -/
theorem sublinear_of_defect (s : FiniteState) (f : Point -> Int)
    (hf : UnitProjection s.toState f) {L : Nat} (hL : 0 < L)
    (hd : Sublinear (totalDefect (heights s.toState f L))) :
    SublinearInt (fun N => missCount s.toState (window L) (window L) (N - window L)) := by
  intro q hq
  obtain ⟨N0, hN⟩ := sublinear_zero_of_defect s f hf hL hd q hq
  refine ⟨N0, fun N hn => ⟨missCount_nonneg _ _ _ _, ?_⟩⟩
  have hm := Int.mul_le_mul_of_nonneg_left (missCount_suffix_le s.toState (window L) N)
    (show (0 : Int) <= q by omega)
  exact Int.le_trans hm (hN N hn).2

theorem x_unitProjection (s : State) : UnitProjection s (fun p => p.1) := by
  intro n
  change -1 <= (move (run s n).pos (turn ((run s n).board (run s n).pos) (run s n).dir)).1 -
      (run s n).pos.1 ∧
    (move (run s n).pos (turn ((run s n).board (run s n).pos) (run s n).dir)).1 -
      (run s n).pos.1 <= 1
  cases turn ((run s n).board (run s n).pos) (run s n).dir <;> simp [move] <;> omega

/-- Kernel-computed non-vacuity: a fixed coordinate projection, L=1, N=8. -/
theorem blank_budget_example :
    missCount blank (window 1) (window 1) (8 - window 1) <=
      2 * (1 : Int) * (totalDefect (heights blank (fun p => p.1) 1) (ceilBlocks 8 1) : Int) := by
  decide

/-- The same concrete orbit also instantiates the universal theorem for every N. -/
theorem blank_budget_all (N : Nat) :
    missCount blank (window 1) (window 1) (N - window 1) <=
      2 * (1 : Int) * (totalDefect (heights blank (fun p => p.1) 1) (ceilBlocks N 1) : Int) := by
  have h := directional_budget finiteBlank (fun p => p.1) (x_unitProjection _) (by decide : 0 < 1) N
  rw [finiteBlank_toState] at h
  simpa [finiteBlank, unique] using h

end LangtonsAnt.DirectionalBudget
