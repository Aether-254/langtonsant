import BoundedMemory
import PeriodicGrowth

/-!
# Exact cache accounting and the finite-support periodic-growth obstruction

The recent window contains read positions at times `j < n` with `n <= j + W`.
All colors come from the full board; evicted cells are not erased from the orbit.
The cache accounting is adapted from the independently checked research scratch
file `CacheBalance.lean`. No scratch file is imported.

Status: exact cache and full-board balance are proved here. The arbitrary
read-suffix predictor-cycle positivity lemma and the unconditional C2 bound are
NOT proved. `black_bound_of_event_bound` isolates the missing event-count bound
as an explicit premise, under a different name. The highway-growth obstruction
applies to actual `HighwayFrom` witnesses, not arbitrary predictor cycles.

`missCount s W W (N - W)` is the paper's E_W(N), when W <= N.
All balance equations and lower bounds use Int, not truncated Nat subtraction.
-/

namespace LangtonsAnt.BlackCountBound

def unique {a : Type} [DecidableEq a] : List a -> List a
  | [] => []
  | x :: xs => if x ∈ xs then unique xs else x :: unique xs

@[simp] theorem mem_unique {a : Type} [DecidableEq a] (x : a) (xs : List a) :
    x ∈ unique xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons y ys ih =>
      by_cases hy : y ∈ ys
      · simp only [unique, ite_eq_left hy, ih, List.mem_cons]
        exact ⟨Or.inr, fun h => h.elim (fun e => e.symm ▸ hy) id⟩
      · simp [unique, hy, ih]

theorem nodup_unique {a : Type} [DecidableEq a] (xs : List a) :
    (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
      by_cases hx : x ∈ xs
      · simpa [unique, hx] using ih
      · simp [unique, hx, ih]

def recentCells (s : State) (W n : Nat) : List Point :=
  unique (((List.range n).filter (fun j => decide (n <= j + W))).map
    (fun j => (run s j).pos))

theorem mem_recentCells (s : State) (W n : Nat) (p : Point) :
    p ∈ recentCells s W n ↔
      exists j, j < n ∧ n <= j + W ∧ (run s j).pos = p := by
  simp [recentCells, List.mem_map, List.mem_filter, and_assoc]

theorem nodup_recentCells (s : State) (W n : Nat) :
    (recentCells s W n).Nodup := nodup_unique _

theorem current_mem_recent_next (s : State) {W : Nat} (hW : 0 < W) (n : Nat) :
    (run s n).pos ∈ recentCells s W (n + 1) := by
  exact (mem_recentCells _ _ _ _).mpr ⟨n, by omega, by omega, rfl⟩

theorem recent_next_subset (s : State) (W n : Nat) (p : Point)
    (h : p ∈ recentCells s W (n + 1)) :
    p = (run s n).pos ∨ p ∈ recentCells s W n := by
  obtain ⟨j, hj, hW, hp⟩ := (mem_recentCells _ _ _ _).mp h
  by_cases he : j = n
  · exact Or.inl (hp.symm.trans (congrArg (fun k => (run s k).pos) he))
  · exact Or.inr ((mem_recentCells _ _ _ _).mpr ⟨j, by omega, by omega, hp⟩)

def bitInt (b : Bool) : Int := if b then 1 else 0
def turnMass (b : Bool) : Int := 1 - 2 * bitInt b

def insertPoint (p : Point) (xs : List Point) : List Point :=
  if p ∈ xs then xs else p :: xs

@[simp] theorem mem_insertPoint (p q : Point) (xs : List Point) :
    q ∈ insertPoint p xs ↔ q = p ∨ q ∈ xs := by
  by_cases hp : p ∈ xs
  · simp only [insertPoint, ite_eq_left hp]
    exact ⟨Or.inr, fun h => h.elim (fun e => e.symm ▸ hp) id⟩
  · simp [insertPoint, hp]

theorem nodup_insertPoint (p : Point) {xs : List Point} (h : xs.Nodup) :
    (insertPoint p xs).Nodup := by
  by_cases hp : p ∈ xs <;> simp [insertPoint, hp, h]

theorem count_flip_away (b : Board) (p : Point) {xs : List Point}
    (hp : p ∉ xs) : xs.countP (flip b p) = xs.countP b := by
  apply List.countP_congr
  intro q hq
  have hqp : q ≠ p := fun he => hp (he ▸ hq)
  simp [flip, hqp]

theorem count_flip (b : Board) (p : Point) {xs : List Point}
    (hnd : xs.Nodup) :
    (xs.countP (flip b p) : Int) - (xs.countP b : Int) =
      if p ∈ xs then turnMass (b p) else 0 := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
      obtain ⟨hq, ht⟩ := List.nodup_cons.mp hnd
      by_cases he : q = p
      · subst q
        have hf := count_flip_away b p hq
        cases hb : b p <;>
          simp [flip_same, hf, hb, turnMass, bitInt] <;> omega
      · have hf := ih ht
        have he' : p ≠ q := Ne.symm he
        simp only [List.mem_cons, he', false_or]
        simp only [List.countP_cons, flip_other b he]
        cases b q <;> simp only [Bool.false_eq_true, ite_false, ite_true,
          Nat.add_zero, Int.natCast_add, Int.natCast_one] <;> omega

theorem expanded_cache_count (b : Board) (p : Point) {xs : List Point}
    (hnd : xs.Nodup) :
    ((insertPoint p xs).countP (flip b p) : Int) - (xs.countP b : Int) =
      turnMass (b p) + bitInt (b p && decide (p ∉ xs)) := by
  have hf := count_flip b p hnd
  by_cases hp : p ∈ xs
  · simpa [insertPoint, hp, bitInt] using hf
  · have ha := count_flip_away b p hp
    cases hb : b p <;>
      simp [insertPoint, hp, flip_same, ha, hb, turnMass, bitInt] <;> omega

theorem moving_cache_balance (b : Board) (p : Point) (xs ys : List Point)
    (hx : xs.Nodup) (hy : ys.Nodup) (hp : p ∈ ys)
    (hsub : forall q, q ∈ ys -> q = p ∨ q ∈ xs) :
    ((ys.filter (flip b p)).length : Int) - ((xs.filter b).length : Int) =
      turnMass (b p) + bitInt (b p && decide (p ∉ xs)) -
      (((xs.filter (flip b p)).filter (fun q => decide (q ∉ ys))).length : Int) := by
  let zs := insertPoint p xs
  have hz : zs.Nodup := nodup_insertPoint p hx
  have livePerm : ((zs.filter (flip b p)).filter (fun q => decide (q ∈ ys))).Perm
      (ys.filter (flip b p)) := by
    apply (List.perm_ext_iff_of_nodup ((hz.filter _).filter _) (hy.filter _)).mpr
    intro q
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨(mem_insertPoint _ _ _).mpr (hsub q h.1), h.2⟩, h.1⟩
  have evictPerm : ((zs.filter (flip b p)).filter (fun q => decide (q ∉ ys))).Perm
      ((xs.filter (flip b p)).filter (fun q => decide (q ∉ ys))) := by
    apply (List.perm_ext_iff_of_nodup ((hz.filter _).filter _) ((hx.filter _).filter _)).mpr
    intro q
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · intro h
      have hq : q ∈ xs := by
        rcases (mem_insertPoint _ _ _).mp h.1.1 with he | he
        · exact False.elim (h.2 (he.symm ▸ hp))
        · exact he
      exact ⟨⟨hq, h.1.2⟩, h.2⟩
    · intro h
      exact ⟨⟨(mem_insertPoint _ _ _).mpr (Or.inr h.1.1), h.1.2⟩, h.2⟩
  have hpart : (zs.filter (flip b p)).length =
      ((zs.filter (flip b p)).filter (fun q => decide (q ∈ ys))).length +
      ((zs.filter (flip b p)).filter (fun q => decide (q ∉ ys))).length := by
    simpa [List.countP_eq_length_filter] using
      (List.length_eq_countP_add_countP (fun q => decide (q ∈ ys))
        (l := zs.filter (flip b p)))
  have he := expanded_cache_count b p hx
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at he
  have hl := livePerm.length_eq
  have hv := evictPerm.length_eq
  change ((zs.filter (flip b p)).length : Int) - _ = _ at he
  omega

def cacheLive (s : State) (W n : Nat) : List Point :=
  (recentCells s W n).filter (run s n).board

def cacheEviction (s : State) (W n : Nat) : List Point :=
  ((recentCells s W n).filter (run s (n + 1)).board).filter
    (fun p => decide (p ∉ recentCells s W (n + 1)))

def cacheMissBit (s : State) (W n : Nat) : Bool :=
  readColor s n && decide ((run s n).pos ∉ recentCells s W n)

theorem cache_balance (s : State) {W : Nat} (hW : 0 < W) (n : Nat) :
    ((cacheLive s W (n + 1)).length : Int) - ((cacheLive s W n).length : Int) =
      1 - 2 * bitInt (readColor s n) + bitInt (cacheMissBit s W n) -
      ((cacheEviction s W n).length : Int) := by
  have h := moving_cache_balance (run s n).board (run s n).pos
    (recentCells s W n) (recentCells s W (n + 1))
    (nodup_recentCells _ _ _) (nodup_recentCells _ _ _)
    (current_mem_recent_next s hW n) (recent_next_subset s W n)
  simpa only [cacheLive, cacheEviction, cacheMissBit, run_succ, step,
    readColor, turnMass] using h

theorem cacheMissBitC_iff (s : State) (W n : Nat) :
    cacheMissBit s W n = true ↔ readColor s n = true ∧
      ¬(exists j, j < n ∧ n <= j + W ∧ (run s j).pos = (run s n).pos) := by
  simp [cacheMissBit, mem_recentCells]

theorem recentCells_length_le (s : State) (W n : Nat) :
    (recentCells s W n).length <= W := by
  have hsub : recentCells s W n ⊆
      (List.range W).map (fun j => (run s (n - (j + 1))).pos) := by
    intro p hp
    obtain ⟨j, hj, hW, he⟩ := (mem_recentCells _ _ _ _).mp hp
    apply List.mem_map.mpr
    refine ⟨n - j - 1, List.mem_range.mpr (by omega), ?_⟩
    have ht : n - (n - j - 1 + 1) = j := by omega
    simpa only [ht] using he
  have h := (nodup_recentCells s W n).length_le_of_subset hsub
  simpa only [List.length_map, List.length_range] using h

theorem cacheLive_length_le (s : State) (W n : Nat) :
    (cacheLive s W n).length <= W :=
  Nat.le_trans (List.length_filter_le _ _) (recentCells_length_le s W n)

theorem cacheEviction_position (s : State) (W n : Nat) (p : Point)
    (hp : p ∈ cacheEviction s W n) : p = (run s (n - W)).pos := by
  obtain ⟨hpf, hn⟩ := List.mem_filter.mp hp
  obtain ⟨hv, _⟩ := List.mem_filter.mp hpf
  have hn' : p ∉ recentCells s W (n + 1) := of_decide_eq_true hn
  obtain ⟨j, hj, hW, he⟩ := (mem_recentCells _ _ _ _).mp hv
  have hbound : ¬n + 1 <= j + W := by
    intro h
    exact hn' ((mem_recentCells _ _ _ _).mpr ⟨j, by omega, h, he⟩)
  have ht : j = n - W := by omega
  exact he.symm.trans (congrArg (fun k => (run s k).pos) ht)

theorem cacheEviction_length_le_one (s : State) (W n : Nat) :
    (cacheEviction s W n).length <= 1 := by
  have hn : (cacheEviction s W n).Nodup :=
    ((nodup_recentCells s W n).filter _).filter _
  have hsub : cacheEviction s W n ⊆ [(run s (n - W)).pos] := by
    intro p hp
    simpa only [List.mem_singleton] using cacheEviction_position s W n p hp
  exact hn.length_le_of_subset hsub

def sumFrom (f : Nat -> Int) (a : Nat) : Nat -> Int
  | 0 => 0
  | k + 1 => sumFrom f a k + f (a + k)

theorem cache_balance_interval (s : State) {W : Nat} (hW : 0 < W) (a N : Nat) :
    ((cacheLive s W (a + N)).length : Int) - ((cacheLive s W a).length : Int) =
      sumFrom (fun n => turnMass (readColor s n)) a N +
      sumFrom (fun n => bitInt (cacheMissBit s W n)) a N -
      sumFrom (fun n => ((cacheEviction s W n).length : Int)) a N := by
  induction N with
  | zero => simp [sumFrom]
  | succ k ih =>
      have h := cache_balance s hW (a + k)
      simp only [sumFrom, Nat.add_succ, Nat.add_zero, turnMass] at ih h ⊢
      omega

/-- Signed sums use integers: the paper bound must not use truncated subtraction. -/
theorem sumFrom_eq_range (f : Nat -> Int) (a N : Nat) :
    sumFrom f a N = ((List.range N).map (fun i => f (a + i))).sum := by
  induction N with
  | zero => simp [sumFrom]
  | succ k ih =>
      simp only [sumFrom, List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ih]

theorem sumFrom_add (f : Nat -> Int) (a k n : Nat) :
    sumFrom f a (k + n) = sumFrom f a k + sumFrom f (a + k) n := by
  induction n with
  | zero => simp [sumFrom]
  | succ n ih =>
      change sumFrom f a ((k + n) + 1) = _
      rw [sumFrom, sumFrom, ih]
      simp only [Nat.add_assoc, Int.add_assoc]

theorem turnMass_eq_turnSign (b : Bool) : turnMass b = turnSign b := by
  cases b <;> rfl

theorem black_balance_interval (s : FiniteState) (hnd : s.black.Nodup) (a N : Nat) :
    ((s.run (a + N)).black.length : Int) - ((s.run a).black.length : Int) =
      sumFrom (fun n => turnMass (readColor s.toState n)) a N := by
  have h0 := s.black_length_run hnd a
  have h1 := s.black_length_run hnd (a + N)
  have hs := sumFrom_add (fun n => turnMass (readColor s.toState n)) 0 a N
  simp only [sumFrom_eq_range, Nat.zero_add, turnMass_eq_turnSign,
    <- wordGrowthInt_eq_sum_turnSign] at hs
  simp only [wordGrowthInt_eq_sum_turnSign] at h0 h1 hs
  rw [sumFrom_eq_range]
  simp only [turnMass_eq_turnSign]
  omega

def missCount (s : State) (W a N : Nat) : Int :=
  sumFrom (fun n => bitInt (cacheMissBit s W n)) a N

def evictionCount (s : State) (W a N : Nat) : Int :=
  sumFrom (fun n => ((cacheEviction s W n).length : Int)) a N

/-- Exact full-board/cache accounting, without any predictor-cycle assumption. -/
theorem black_cache_balance (s : FiniteState) (hnd : s.black.Nodup)
    {W : Nat} (hW : 0 < W) (a N : Nat) :
    ((s.run (a + N)).black.length : Int) - ((s.run a).black.length : Int) =
      ((cacheLive s.toState W (a + N)).length : Int) -
      ((cacheLive s.toState W a).length : Int) +
      evictionCount s.toState W a N - missCount s.toState W a N := by
  have hc := cache_balance_interval s.toState hW a N
  have hb := black_balance_interval s hnd a N
  unfold evictionCount missCount
  omega

/-- Algebraic reduction only. The event lower bound is an explicit, unproved premise;
this theorem is NOT the unconditional finite-prefix inequality from the paper. -/
theorem black_bound_of_event_bound (s : FiniteState) (hnd : s.black.Nodup)
    {W : Nat} (hW : 0 < W) (a N K : Nat)
    (hevents : (K : Int) <=
      missCount s.toState W a N + evictionCount s.toState W a N) :
    ((s.run a).black.length : Int) - (W : Int) + (K : Int) -
      2 * missCount s.toState W a N <= ((s.run (a + N)).black.length : Int) := by
  have hb := black_cache_balance s hnd hW a N
  have hc := cacheLive_length_le s.toState W a
  have hn : 0 <= ((cacheLive s.toState W (a + N)).length : Int) := by omega
  omega

/-- The real-highway obstruction used by the paper, not its predictor-cycle lemma. -/
theorem finite_highway_growthInt_ge_eight {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    8 <= wordGrowthInt P (fun i => readColor s (T + i)) := by
  have hc := periodic_tail_consistent_at_start hs hP h
  rw [hc.wordGrowthInt_eq_nat]
  exact_mod_cast hc.eight_le_growth

theorem finite_highway_growthInt_ne_zero {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    wordGrowthInt P (fun i => readColor s (T + i)) ≠ 0 := by
  have hg := finite_highway_growthInt_ge_eight hs hP h
  omega

theorem blank_cache_balance_example :
    ((cacheLive blank 1 2).length : Int) - ((cacheLive blank 1 1).length : Int) =
      turnMass (readColor blank 1) + bitInt (cacheMissBit blank 1 1) -
      ((cacheEviction blank 1 1).length : Int) := by decide

/-- A concrete instance of C2, proved by kernel computation, not a general theorem. -/
theorem blank_bound_example :
    ((finiteBlank.run 1).black.length : Int) - 1 + ((4 - 1) / 2^1 : Nat) -
      2 * missCount blank 1 1 3 <= ((finiteBlank.run 4).black.length : Int) := by decide

end LangtonsAnt.BlackCountBound

