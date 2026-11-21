import BoundedMemory

namespace LangtonsAnt

/-- The pose before turn `n`, starting at the origin facing north. -/
def wordTrace (w : Nat -> Bool) : Nat -> Point × Direction
  | 0 => ((0, 0), .north)
  | n + 1 => (move (wordTrace w n).1 (turn (w n) (wordTrace w n).2),
      turn (w n) (wordTrace w n).2)

def wordPos (w : Nat -> Bool) (n : Nat) : Point := (wordTrace w n).1

def wordDrift (P : Nat) (w : Nat -> Bool) : Point := wordPos w P

def scalePoint (v : Point) (t : Int) : Point := (t * v.1, t * v.2)

/-- The unique candidate number of periods separating two occurrences. -/
def priorShift (v p q : Point) : Int :=
  if v.1 = 0 then (p.2 - q.2) / v.2 else (p.1 - q.1) / v.1

/-- Phase `j` visits phase `i`'s cell at an earlier integer period. -/
def EarlierPhase (a : Nat -> Point) (v : Point) (i j : Nat) : Prop :=
  (j < i ∧ a j = a i) ∨
    exists t : Nat, 0 < t ∧ a j = addPoint (a i) (scalePoint v (t : Int))

def checkEarlierPhase (a : Nat -> Point) (v : Point) (i j : Nat) : Bool :=
  decide (j < i ∧ a j = a i) ||
    (decide (0 < priorShift v (a j) (a i)) &&
      decide (a j = addPoint (a i) (scalePoint v (priorShift v (a j) (a i)))))

theorem scalePoint_injective {v : Point} (hv : v ≠ (0, 0)) {m n : Int}
    (h : scalePoint v m = scalePoint v n) : m = n := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [scalePoint] at hx hy
  by_cases hzero : v.1 = 0
  · have hne : v.2 ≠ 0 := by intro he; exact hv (Prod.ext hzero he)
    exact (Int.mul_eq_mul_right_iff hne).mp hy
  · exact (Int.mul_eq_mul_right_iff hzero).mp hx

theorem priorShift_eq {v p q : Point} (hv : v ≠ (0, 0)) {t : Int}
    (h : p = addPoint q (scalePoint v t)) : priorShift v p q = t := by
  subst p
  unfold priorShift
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := by intro he; exact hv (Prod.ext hx he)
    simp only [hx, ite_true, addPoint, scalePoint]
    rw [show q.2 + t * v.2 - q.2 = t * v.2 by omega]
    exact Int.mul_ediv_cancel _ hy
  · simp only [hx, addPoint, scalePoint]
    rw [show q.1 + t * v.1 - q.1 = t * v.1 by omega]
    exact Int.mul_ediv_cancel _ hx

theorem checkEarlierPhase_iff {a : Nat -> Point} {v : Point} (hv : v ≠ (0, 0))
    (i j : Nat) : checkEarlierPhase a v i j = true ↔ EarlierPhase a v i j := by
  simp only [checkEarlierPhase, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨ht, he⟩)
    · exact Or.inl h
    · have hc : ((priorShift v (a j) (a i)).toNat : Int) = priorShift v (a j) (a i) := by omega
      exact Or.inr ⟨(priorShift v (a j) (a i)).toNat, by omega, by simpa only [hc] using he⟩
  · rintro (h | ⟨t, ht, he⟩)
    · exact Or.inl h
    · have hs := priorShift_eq hv he
      exact Or.inr ⟨by omega, by simpa [hs] using he⟩

/-- Each phase occurs at most once among the earlier visits, since the drift is nonzero. -/
def priorPhases (P : Nat) (w : Nat -> Bool) (i : Nat) : List Nat :=
  (List.range P).filter (checkEarlierPhase (wordPos w) (wordDrift P w) i)

def ConsistentWord (P : Nat) (w : Nat -> Bool) : Prop :=
  (wordTrace w P).2 = .north ∧ wordDrift P w ≠ (0, 0) ∧
    forall i, i < P -> w i = decide ((priorPhases P w i).length % 2 = 1)

def checkConsistentWord (P : Nat) (w : Nat -> Bool) : Bool :=
  decide ((wordTrace w P).2 = .north) && decide (wordDrift P w ≠ (0, 0)) &&
    (List.range P).all (fun i => w i == decide ((priorPhases P w i).length % 2 = 1))

theorem checkConsistentWord_iff (P : Nat) (w : Nat -> Bool) :
    checkConsistentWord P w = true ↔ ConsistentWord P w := by
  simp [checkConsistentWord, ConsistentWord, List.all_eq_true, and_assoc]

theorem mem_priorPhases {P : Nat} {w : Nat -> Bool} (hv : wordDrift P w ≠ (0, 0))
    (i j : Nat) : j ∈ priorPhases P w i ↔
      j < P ∧ EarlierPhase (wordPos w) (wordDrift P w) i j := by
  simp [priorPhases, checkEarlierPhase_iff hv]

theorem priorPhases_nodup (P : Nat) (w : Nat -> Bool) (i : Nat) :
    (priorPhases P w i).Nodup := List.nodup_range.filter _

theorem wordPos_bounds (w : Nat -> Bool) (n : Nat) :
    -(n : Int) <= (wordPos w n).1 ∧ (wordPos w n).1 <= (n : Int) ∧
    -(n : Int) <= (wordPos w n).2 ∧ (wordPos w n).2 <= (n : Int) := by
  induction n with
  | zero => simp [wordPos, wordTrace]
  | succ n ih =>
    simp only [wordPos, wordTrace] at ih ⊢
    cases turn (w n) (wordTrace w n).2 <;>
      simp only [move, Int.natCast_add, Int.natCast_one] <;> omega

/-- A nonzero integer coordinate bounds how many periods can overlap. -/
theorem period_overlap_bound {P i j t : Nat} {w : Nat -> Bool}
    (hi : i < P) (hj : j < P) (hv : wordDrift P w ≠ (0, 0))
    (he : wordPos w j = addPoint (wordPos w i) (scalePoint (wordDrift P w) (t : Int))) :
    t <= 2 * P := by
  have bi := wordPos_bounds w i
  have bj := wordPos_bounds w j
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  simp only [addPoint, scalePoint] at hx hy
  have coord (x : Int) (hne : x ≠ 0) :
      (t : Int) <= (t : Int) * x ∨ (t : Int) * x <= -(t : Int) := by
    by_cases hp : 0 < x
    · left
      have := Int.mul_le_mul_of_nonneg_left (show 1 <= x by omega) (show 0 <= (t : Int) by omega)
      simpa using this
    · right
      have := Int.mul_le_mul_of_nonneg_left (show x <= -1 by omega) (show 0 <= (t : Int) by omega)
      simpa using this
  by_cases hzero : (wordDrift P w).1 = 0
  · have hne : (wordDrift P w).2 ≠ 0 := by intro he; exact hv (Prod.ext hzero he)
    rcases coord _ hne with h | h <;> omega
  · rcases coord _ hzero with h | h <;> omega

theorem wordTrace_axis (w : Nat -> Bool) (n : Nat) :
    (wordTrace w n).2.horizontal = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht (c : Bool) (d : Direction) : (turn c d).horizontal = !d.horizontal := by
      cases c <;> cases d <;> rfl
    simp only [wordTrace, ht, ih]
    by_cases hn : n % 2 = 1
    · simp [hn, show (n + 1) % 2 = 0 by omega]
    · simp [hn, show (n + 1) % 2 = 1 by omega]

theorem ConsistentWord.even {P : Nat} {w : Nat -> Bool} (h : ConsistentWord P w) :
    P % 2 = 0 := by
  have ha := wordTrace_axis w P
  rw [h.1] at ha
  simp only [Direction.horizontal] at ha
  have : ¬ P % 2 = 1 := by
    intro hp
    simp [hp] at ha
  omega

theorem no_consistent_word_odd {P : Nat} (hP : P % 2 = 1) (w : Nat -> Bool) :
    ¬ ConsistentWord P w := by
  intro h
  have := h.even
  omega

/-- Integer-period coordinates for the two-sided path; phases satisfy `j < P`. -/
def biPeriodicPos (P : Nat) (w : Nat -> Bool) (k : Int) (j : Nat) : Point :=
  addPoint (wordPos w j) (scalePoint (wordDrift P w) k)

theorem earlierPhase_iff_integer_period {P i j : Nat} {w : Nat -> Bool}
    (hi : i < P) (hj : j < P) :
    EarlierPhase (wordPos w) (wordDrift P w) i j ↔
      exists k : Int, k * (P : Int) + (j : Int) < (i : Int) ∧
        biPeriodicPos P w k j = wordPos w i := by
  constructor
  · rintro (⟨hji, he⟩ | ⟨t, ht, he⟩)
    · exact ⟨0, by omega, by simpa [biPeriodicPos, scalePoint] using he⟩
    · refine ⟨-(t : Int), ?_, ?_⟩
      · have hh := Int.mul_le_mul_of_nonneg_right (show -(t : Int) <= -1 by omega)
          (show 0 <= (P : Int) by omega)
        simp only [Int.neg_mul, Int.one_mul] at hh
        simp only [Int.neg_mul]
        omega
      · rw [biPeriodicPos, he]
        apply Prod.ext <;> simp only [addPoint, scalePoint, Int.neg_mul] <;> omega
  · rintro ⟨k, htime, he⟩
    have hk : k <= 0 := by
      by_cases hn : 1 <= k
      · have hh := Int.mul_le_mul_of_nonneg_right hn (show 0 <= (P : Int) by omega)
        simp only [Int.one_mul] at hh
        omega
      · omega
    by_cases hz : k = 0
    · have hji : j < i := by
        simp only [hz, Int.zero_mul, Int.zero_add] at htime
        omega
      exact Or.inl ⟨hji, by simpa [biPeriodicPos, hz, scalePoint] using he⟩
    · refine Or.inr ⟨(-k).toNat, by omega, ?_⟩
      have hc : ((-k).toNat : Int) = -k := by omega
      apply Prod.ext
      · have hh := congrArg Prod.fst he
        simp only [biPeriodicPos, addPoint, scalePoint, hc, Int.neg_mul] at hh ⊢
        omega
      · have hh := congrArg Prod.snd he
        simp only [biPeriodicPos, addPoint, scalePoint, hc, Int.neg_mul] at hh ⊢
        omega

theorem biPeriodicPos_injective_period {P : Nat} {w : Nat -> Bool}
    (hv : wordDrift P w ≠ (0, 0)) {k l : Int} {j : Nat}
    (he : biPeriodicPos P w k j = biPeriodicPos P w l j) : k = l := by
  apply scalePoint_injective hv
  apply Prod.ext
  · have hh := congrArg Prod.fst he
    simp only [biPeriodicPos, addPoint] at hh
    omega
  · have hh := congrArg Prod.snd he
    simp only [biPeriodicPos, addPoint] at hh
    omega

theorem mem_priorPhases_iff_integer_period {P i j : Nat} {w : Nat -> Bool}
    (hv : wordDrift P w ≠ (0, 0)) (hi : i < P) (hj : j < P) :
    j ∈ priorPhases P w i ↔
      exists k : Int, k * (P : Int) + (j : Int) < (i : Int) ∧
        biPeriodicPos P w k j = wordPos w i := by
  rw [mem_priorPhases hv, and_iff_right hj, earlierPhase_iff_integer_period hi hj]

theorem wordTrace_congr {n : Nat} {w u : Nat -> Bool}
    (h : forall i, i < n -> w i = u i) : wordTrace w n = wordTrace u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordTrace, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem priorPhases_congr {P : Nat} {w u : Nat -> Bool}
    (h : forall j, j < P -> w j = u j) {i : Nat} (hi : i < P) :
    priorPhases P w i = priorPhases P u i := by
  have ht (n : Nat) (hn : n <= P) : wordPos w n = wordPos u n :=
    congrArg Prod.fst (wordTrace_congr (fun j hj => h j (by omega)))
  apply List.filter_congr
  intro j hj
  have hjP := List.mem_range.mp hj
  simp only [checkEarlierPhase, wordDrift, ht P (by omega), ht i (by omega), ht j (by omega)]
  rfl

theorem ConsistentWord.congr {P : Nat} {w u : Nat -> Bool}
    (h : ConsistentWord P w) (he : forall j, j < P -> w j = u j) : ConsistentWord P u := by
  have ht := wordTrace_congr he
  refine ⟨?_, ?_, ?_⟩
  · rw [← ht]
    exact h.1
  · simpa only [wordDrift, wordPos, ht] using h.2.1
  · intro i hi
    rw [← he i hi, ← priorPhases_congr he hi]
    exact h.2.2 i hi

end LangtonsAnt
