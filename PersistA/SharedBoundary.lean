import PersistA.TwoGateDecomposition
import TwoCellDiagonalExtremal
import PeriodicWordRealization

/-!
The shared-boundary equations of research round 70, in the coordinates of
`wordPos`. Bits are added with Boolean xor. A block retains its actual word,
phase interval, and translated physical positions; its visit counts are not
free variables. Initial boards are constrained only on visited cells.
-/

namespace LangtonsAnt.PersistA.SharedBoundary

def advance (p : Point) (k : Int) : Point := (p.1 + k, p.2 - k)

@[simp] theorem advance_zero (p : Point) : advance p 0 = p := by
  cases p
  simp [advance]

@[simp] theorem advance_add (p : Point) (k l : Int) :
    advance (advance p k) l = advance p (k + l) := by
  apply Prod.ext <;> simp only [advance] <;> omega

/-- Membership in the full-drift half-line `p + 2 * j * (1,-1)`, `j >= 0`. -/
def onRay (p q : Point) : Bool :=
  decide (p.1 ≤ q.1 ∧ (q.1 - p.1) % 2 = 0 ∧ p.1 + p.2 = q.1 + q.2)

theorem onRay_iff (p q : Point) :
    onRay p q = true ↔ ∃ j : Nat, q = advance p (2 * (j : Int)) := by
  simp only [onRay, decide_eq_true_eq]
  constructor
  · rintro ⟨hle, hmod, hsum⟩
    refine ⟨((q.1 - p.1) / 2).toNat, ?_⟩
    apply Prod.ext <;> simp only [advance] <;> omega
  · rintro ⟨j, rfl⟩
    simp only [advance]
    omega

theorem onRay_translate (p q : Point) (k : Int) :
    onRay (advance p k) (advance q k) = onRay p q := by
  unfold onRay
  congr 1
  simp only [advance]
  apply propext
  omega

theorem onRay_split (p q : Point) :
    onRay p q = (decide (q = p) || onRay (advance p 2) q) := by
  apply Bool.eq_iff_iff.mpr
  change (onRay p q = true) ↔ _
  simp only [Bool.or_eq_true, onRay, decide_eq_true_eq]
  simp only [advance]
  constructor
  · intro h
    by_cases he : q = p
    · exact Or.inl he
    · right
      have hn : q.1 ≠ p.1 := by
        intro hx
        exact he (Prod.ext hx (by omega))
      omega
  · rintro (rfl | h) <;> omega

theorem onRay_strict_ne (p q : Point) (h : onRay (advance p 2) q = true) : q ≠ p := by
  have hx : (advance p 2).1 ≤ q.1 := (of_decide_eq_true h).1
  intro he
  rw [he] at hx
  simp only [advance] at hx
  omega

private theorem countP_or {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = true → g x = false) :
    xs.countP (fun x => f x || g x) = xs.countP f + xs.countP g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      ih (fun y hy => h y (by simp [hy]))]
    have hx := h x (by simp)
    cases hf : f x <;> cases hg : g x <;> simp_all <;> omega

private theorem countP_prefix (n i : Nat) (hi : i ≤ n) (f : Nat → Bool) :
    (List.range n).countP (fun j => decide (j < i) && f j) =
      (List.range i).countP f := by
  rw [show n = i + (n - i) by omega, List.range_add, List.countP_append,
    List.countP_map]
  have hleft : (List.range i).countP (fun j => decide (j < i) && f j) =
      (List.range i).countP f := by
    apply List.countP_congr
    intro j hj
    simp [List.mem_range.mp hj]
  have hright : (List.range (n - i)).countP
      ((fun j => decide (j < i) && f j) ∘ (i + ·)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro j _
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega
  rw [hleft, hright, Nat.add_zero]

def bit (n : Nat) : Bool := decide (n % 2 = 1)

@[simp] theorem bit_zero : bit 0 = false := rfl

theorem bit_add (m n : Nat) : bit (m + n) = (bit m ^^ bit n) := by
  unfold bit
  have hadd := Nat.add_mod m n 2
  by_cases hm : m % 2 = 1 <;> by_cases hn : n % 2 = 1 <;>
    simp [hm, hn] <;>
    omega

/-- An interval of an actual prescribed word, in a translated coordinate frame. -/
structure Block where
  word : Nat → Bool
  start : Nat
  length : Nat
  origin : Point

def Block.pos (b : Block) (i : Nat) : Point :=
  subPoint (wordPos b.word (b.start + i)) b.origin

def Block.color (b : Block) (i : Nat) : Bool := b.word (b.start + i)

def Block.visits (b : Block) (n : Nat) (p : Point) : Nat :=
  (List.range n).countP (fun i => decide (b.pos i = p))

def Block.N (b : Block) (p : Point) : Nat := b.visits b.length p

/-- This counts individual visits on the half-line, including multiplicity. -/
def Block.tailCount (b : Block) (p : Point) : Nat :=
  (List.range b.length).countP (fun i => onRay p (b.pos i))

def Block.T (b : Block) (p : Point) : Bool := bit (b.tailCount p)

def Block.Support (b : Block) (p : Point) : Prop :=
  ∃ i, i < b.length ∧ b.pos i = p

/-- The initial board and every preceding flip must explain every read. -/
def Block.Legal (b : Block) (a : Board) : Prop :=
  ∀ i, i < b.length → b.color i = (a (b.pos i) ^^ bit (b.visits i (b.pos i)))

theorem Block.support_iff (b : Block) (p : Point) : b.Support p ↔ 0 < b.N p := by
  simp [Block.Support, Block.N, Block.visits, List.countP_pos_iff]

theorem Block.visits_succ (b : Block) (n : Nat) (p : Point) :
    b.visits (n + 1) p = b.visits n p + if b.pos n = p then 1 else 0 := by
  simp [Block.visits, List.range_succ]

theorem Block.tailCount_split (b : Block) (p : Point) :
    b.tailCount p = b.N p + b.tailCount (advance p 2) := by
  unfold Block.tailCount Block.N Block.visits
  have he : (fun i => onRay p (b.pos i)) =
      (fun i => decide (b.pos i = p) || onRay (advance p 2) (b.pos i)) := by
    funext i
    exact onRay_split p (b.pos i)
  rw [he]
  apply countP_or
  intro i _ hi
  have hp : b.pos i = p := of_decide_eq_true hi
  apply Bool.eq_false_iff.mpr
  intro hr
  exact onRay_strict_ne p (b.pos i) hr hp

theorem Block.T_split (b : Block) (p : Point) :
    b.T p = (bit (b.N p) ^^ b.T (advance p 2)) := by
  simp only [Block.T, b.tailCount_split p, bit_add]

theorem Block.first_visit_color {b : Block} {a : Board} (h : b.Legal a)
    {i : Nat} (hi : i < b.length) (hf : b.visits i (b.pos i) = 0) :
    a (b.pos i) = b.color i := by
  simpa [hf] using (h i hi).symm

theorem Block.tailCount_eventually_zero (b : Block) (p : Point) :
    ∃ K : Nat, b.tailCount (advance p (2 * (K : Int))) = 0 := by
  let z : Int := (b.start + b.length : Nat) - b.origin.1 - p.1
  refine ⟨z.toNat + 1, ?_⟩
  apply List.countP_eq_zero.mpr
  intro i hi hr
  have hib := List.mem_range.mp hi
  have hb := (wordPos_bounds b.word (b.start + i)).2.1
  have hx := (of_decide_eq_true hr).1
  simp only [advance, Block.pos, subPoint, Int.natCast_add, Int.natCast_one] at hx
  dsimp [z] at hx
  omega

/-- Finite truncation of the literal half-line sum, with its exact remainder. -/
theorem Block.tailCount_sum (b : Block) (p : Point) (K : Nat) :
    b.tailCount p =
      ((List.range K).map (fun j : Nat => b.N (advance p (2 * (j : Int))))).sum +
        b.tailCount (advance p (2 * (K : Int))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [ih, b.tailCount_split (advance p (2 * (K : Int))), advance_add]
    have he : 2 * (K : Int) + 2 = 2 * ((K + 1 : Nat) : Int) := by omega
    rw [he]
    omega

/-- Thus `T` really is the mod-two finite sum of the visit multiplicities. -/
theorem Block.T_eq_finite_sum (b : Block) (p : Point) :
    ∃ K : Nat, b.T p =
      bit (((List.range K).map (fun j : Nat => b.N (advance p (2 * (j : Int))))).sum) := by
  obtain ⟨K, hK⟩ := b.tailCount_eventually_zero p
  refine ⟨K, ?_⟩
  unfold Block.T
  rw [b.tailCount_sum p K, hK, Nat.add_zero]

def U (w : Nat → Bool) (cut : Nat) : Block := ⟨w, 0, cut, (0, 0)⟩

def V (w : Nat → Bool) (P cut : Nat) : Block := ⟨w, cut, P - cut, (1, -1)⟩

@[simp] theorem U_length (w : Nat → Bool) (cut : Nat) : (U w cut).length = cut := rfl

@[simp] theorem V_length (w : Nat → Bool) (P cut : Nat) :
    (V w P cut).length = P - cut := rfl

@[simp] theorem U_color (w : Nat → Bool) (cut i : Nat) : (U w cut).color i = w i := by
  simp [U, Block.color]

@[simp] theorem V_color (w : Nat → Bool) (P cut i : Nat) :
    (V w P cut).color i = w (cut + i) := rfl

@[simp] theorem U_pos (w : Nat → Bool) (cut i : Nat) :
    (U w cut).pos i = wordPos w i := by
  simp [U, Block.pos, subPoint]

@[simp] theorem V_pos (w : Nat → Bool) (P cut i : Nat) :
    (V w P cut).pos i = advance (wordPos w (cut + i)) (-1) := by
  apply Prod.ext <;> simp only [V, Block.pos, subPoint, advance] <;> omega

private theorem countP_range_split (P cut : Nat) (hc : cut ≤ P) (f : Nat → Bool) :
    (List.range P).countP f = (List.range cut).countP f +
      (List.range (P - cut)).countP (fun i => f (cut + i)) := by
  conv => lhs; rw [show P = cut + (P - cut) by omega]
  rw [List.range_add, List.countP_append, List.countP_map]
  rfl

theorem whole_tail_split {P cut : Nat} (hc : cut ≤ P) (w : Nat → Bool) (p : Point) :
    (U w P).tailCount p = (U w cut).tailCount p +
      (V w P cut).tailCount (advance p (-1)) := by
  simp only [Block.tailCount, U_pos, V_pos, onRay_translate]
  exact countP_range_split P cut hc _

theorem whole_visits_split (w : Nat → Bool) (P cut i : Nat) (p : Point) :
    (U w P).visits (cut + i) p = (U w cut).N p +
      (V w P cut).visits i (advance p (-1)) := by
  simp only [Block.N, Block.visits, U_length, U_pos, V_pos, List.range_add,
    List.countP_append, List.countP_map]
  congr 1
  apply List.countP_congr
  intro j _
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · intro he
    rw [he]
  · intro he
    apply Prod.ext
    · have hx := congrArg Prod.fst he
      simp only [advance] at hx
      omega
    · have hy := congrArg Prod.snd he
      simp only [advance] at hy
      omega

private theorem earlier_iff_ray (w : Nat → Bool) (i j : Nat) :
    EarlierPhase (wordPos w) (2, -2) i j ↔
      (j < i ∧ wordPos w j = wordPos w i) ∨
        onRay (advance (wordPos w i) 2) (wordPos w j) = true := by
  rw [EarlierPhase, onRay_iff]
  apply or_congr_right
  constructor
  · rintro ⟨t, ht, he⟩
    refine ⟨t - 1, ?_⟩
    rw [he]
    apply Prod.ext <;> simp only [addPoint, scalePoint, advance] <;> omega
  · rintro ⟨t, he⟩
    refine ⟨t + 1, by omega, ?_⟩
    rw [he]
    apply Prod.ext <;> simp only [addPoint, scalePoint, advance, Int.natCast_add,
      Int.natCast_one] <;> omega

/-- The repository's stable rank is the exact number of preceding physical flips. -/
theorem stableRank_eq_visits_add_tail {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hi : i < P) :
    Drift.stableRank P w i = (U w P).visits i (wordPos w i) +
      (U w P).tailCount (advance (wordPos w i) 2) := by
  rw [Drift.stableRank, priorPhases, ← List.countP_eq_length_filter, hd]
  have he : (List.range P).countP (checkEarlierPhase (wordPos w) (2, -2) i) =
      (List.range P).countP (fun j =>
        (decide (j < i) && decide (wordPos w j = wordPos w i)) ||
          onRay (advance (wordPos w i) 2) (wordPos w j)) := by
    apply List.countP_congr
    intro j _
    rw [checkEarlierPhase_iff (by decide), earlier_iff_ray]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [he, countP_or, countP_prefix P i (by omega)]
  · simp only [Block.visits, Block.tailCount, U_length, U_pos]
  · intro j _ hj
    have hp : wordPos w j = wordPos w i :=
      (show j < i ∧ wordPos w j = wordPos w i from
        by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hj).2
    apply Bool.eq_false_iff.mpr
    intro hr
    exact onRay_strict_ne _ _ hr hp

theorem stableRank_U {P cut i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hc : cut ≤ P) (hi : i < cut) :
    Drift.stableRank P w i = (U w cut).visits i ((U w cut).pos i) +
      (U w cut).tailCount (advance ((U w cut).pos i) 2) +
        (V w P cut).tailCount (advance ((U w cut).pos i) 1) := by
  rw [stableRank_eq_visits_add_tail hd (by omega), whole_tail_split hc]
  simp only [U_pos, advance_add]
  exact Nat.add_assoc _ _ _ |>.symm

theorem stableRank_V {P cut i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hc : cut ≤ P) (hi : i < P - cut) :
    Drift.stableRank P w (cut + i) =
      (V w P cut).visits i ((V w P cut).pos i) +
        (U w cut).tailCount (advance ((V w P cut).pos i) 1) +
          (V w P cut).tailCount (advance ((V w P cut).pos i) 2) := by
  rw [stableRank_eq_visits_add_tail hd (by omega), whole_visits_split,
    whole_tail_split hc]
  simp only [V_pos, advance_add]
  have h := (U w cut).tailCount_split (wordPos w (cut + i))
  simp only [show (-1 : Int) + 1 = 0 by decide, advance_zero,
    show (-1 : Int) + 2 = 1 by decide, show (2 : Int) + -1 = 1 by decide]
  omega

/-- The forced board at the start of the first block. -/
def initialU (w : Nat → Bool) (P cut : Nat) : Board := fun p =>
  (U w cut).T (advance p 2) ^^ (V w P cut).T (advance p 1)

/-- The board at the second block, expressed in its translated frame. -/
def initialV (w : Nat → Bool) (P cut : Nat) : Board := fun p =>
  (V w P cut).T (advance p 2) ^^ (U w cut).T (advance p 1)

theorem stableRank_U_bit {P cut i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hc : cut ≤ P) (hi : i < cut) :
    bit (Drift.stableRank P w i) =
      (initialU w P cut ((U w cut).pos i) ^^
        bit ((U w cut).visits i ((U w cut).pos i))) := by
  rw [stableRank_U hd hc hi, bit_add, bit_add]
  unfold initialU Block.T
  rw [Bool.xor_assoc]
  exact Bool.xor_comm ..

theorem stableRank_V_bit {P cut i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hc : cut ≤ P) (hi : i < P - cut) :
    bit (Drift.stableRank P w (cut + i)) =
      (initialV w P cut ((V w P cut).pos i) ^^
        bit ((V w P cut).visits i ((V w P cut).pos i))) := by
  rw [stableRank_V hd hc hi, bit_add, bit_add]
  unfold initialV Block.T
  rw [Bool.xor_assoc, Bool.xor_comm (bit ((U w cut).tailCount _))]
  exact Bool.xor_comm ..

theorem consistentWord_iff_initial_legal {P cut : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    (hc : cut ≤ P) :
    ConsistentWord P w ↔
      (U w cut).Legal (initialU w P cut) ∧ (V w P cut).Legal (initialV w P cut) := by
  constructor
  · intro hw
    constructor
    · intro i hi
      rw [U_color]
      exact (Drift.consistentWord_stableRank_color hw (by exact Nat.lt_of_lt_of_le hi hc)).trans
        (stableRank_U_bit hd hc hi)
    · intro i hi
      change w (cut + i) = _
      exact (Drift.consistentWord_stableRank_color hw (by change i < P - cut at hi; omega)).trans
        (stableRank_V_bit hd hc hi)
  · rintro ⟨hu, hv⟩
    refine ⟨hdir, by rw [hd]; decide, ?_⟩
    intro i hi
    change w i = bit (Drift.stableRank P w i)
    by_cases hicut : i < cut
    · rw [stableRank_U_bit hd hc hicut]
      simpa only [U_color] using hu i hicut
    · have hik : i - cut < P - cut := by omega
      have he : cut + (i - cut) = i := by omega
      have hread := hv (i - cut) hik
      have hrank := stableRank_V_bit hd hc hik
      change w (cut + (i - cut)) = _ at hread
      rw [he] at hread hrank
      exact hread.trans hrank.symm

theorem Block.legal_unique_on_support {b : Block} {a c : Board}
    (ha : b.Legal a) (hc : b.Legal c) {p : Point} (hp : b.Support p) : a p = c p := by
  obtain ⟨i, hi, he⟩ := hp
  have h1 := ha i hi
  have h2 := hc i hi
  rw [he] at h1 h2
  have hh := h1.symm.trans h2
  have hh' := congrArg (fun x => x ^^ bit (b.visits i p)) hh
  simpa only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] using hh'

theorem Block.legal_congr_on_support {b : Block} {a c : Board}
    (h : ∀ p, b.Support p → a p = c p) : b.Legal a ↔ b.Legal c := by
  constructor <;> intro hl i hi
  · rw [← h (b.pos i) ⟨i, hi, rfl⟩]
    exact hl i hi
  · rw [h (b.pos i) ⟨i, hi, rfl⟩]
    exact hl i hi

/-- Exactly round 70's two equations; `^^` is addition modulo two. -/
def SharedBoundary (w : Nat → Bool) (P cut : Nat) (aU aV : Board) : Prop :=
  (∀ p, (U w cut).Support p →
    (V w P cut).T (advance p 1) = (aU p ^^ (U w cut).T (advance p 2))) ∧
  (∀ p, (V w P cut).Support p →
    (U w cut).T (advance p 1) = (aV p ^^ (V w P cut).T (advance p 2)))

private theorem xor_solve (x y a : Bool) : (x ^^ y) = a ↔ y = (a ^^ x) := by
  cases x <;> cases y <;> cases a <;> decide

theorem sharedBoundary_iff_boards (w : Nat → Bool) (P cut : Nat) (aU aV : Board) :
    SharedBoundary w P cut aU aV ↔
      (∀ p, (U w cut).Support p → initialU w P cut p = aU p) ∧
      (∀ p, (V w P cut).Support p → initialV w P cut p = aV p) := by
  simp only [SharedBoundary, initialU, initialV, xor_solve]

/-- No condition is imposed on the initial colors of unvisited cells.
The hypotheses on `aU` and `aV` are precisely the paper's internal flip legality. -/
theorem consistentWord_iff_sharedBoundary {P cut : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    (hc : cut ≤ P) {aU aV : Board}
    (hu : (U w cut).Legal aU) (hv : (V w P cut).Legal aV) :
    ConsistentWord P w ↔ SharedBoundary w P cut aU aV := by
  rw [consistentWord_iff_initial_legal hdir hd hc, sharedBoundary_iff_boards]
  constructor
  · rintro ⟨hU, hV⟩
    exact ⟨fun _ hp => Block.legal_unique_on_support hU hu hp,
      fun _ hp => Block.legal_unique_on_support hV hv hp⟩
  · rintro ⟨hU, hV⟩
    exact ⟨(Block.legal_congr_on_support hU).mpr hu,
      (Block.legal_congr_on_support hV).mpr hv⟩

/-- The full criterion also constructs both internally legal boards. -/
theorem consistentWord_iff_exists_sharedBoundary {P cut : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    (hc : cut ≤ P) :
    ConsistentWord P w ↔ ∃ aU aV : Board,
      (U w cut).Legal aU ∧ (V w P cut).Legal aV ∧ SharedBoundary w P cut aU aV := by
  constructor
  · intro hw
    obtain ⟨hu, hv⟩ := (consistentWord_iff_initial_legal hdir hd hc).mp hw
    refine ⟨initialU w P cut, initialV w P cut, hu, hv, ?_⟩
    exact (sharedBoundary_iff_boards ..).mpr ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · rintro ⟨aU, aV, hu, hv, hb⟩
    exact (consistentWord_iff_sharedBoundary hdir hd hc hu hv).mpr hb

/-- `B0(p)` is the full-word forward tail, starting one full drift ahead. -/
theorem initialU_eq_whole_tail {P cut : Nat} (hc : cut ≤ P) (w : Nat → Bool)
    (p : Point) : initialU w P cut p = (U w P).T (advance p 2) := by
  simp only [initialU, Block.T, whole_tail_split hc, bit_add, advance_add]
  rfl

/-- Executing U gives precisely V's board in the frame translated by `(1,-1)`. -/
theorem initialV_eq_after_U (w : Nat → Bool) (P cut : Nat) (p : Point) :
    initialV w P cut p =
      (initialU w P cut (advance p 1) ^^ bit ((U w cut).N (advance p 1))) := by
  unfold initialU initialV
  rw [(U w cut).T_split (advance p 1)]
  simp only [advance_add]
  have shuffle (x y z : Bool) : (y ^^ (z ^^ x)) = (x ^^ y ^^ z) := by
    cases x <;> cases y <;> cases z <;> rfl
  exact shuffle _ _ _

/-- The full-cycle update has the exact spatial translation required in round 70. -/
theorem initialU_period_update {P cut : Nat} (hc : cut ≤ P) (w : Nat → Bool)
    (p : Point) :
    (initialU w P cut p ^^ bit ((U w P).N p)) =
      initialU w P cut (advance p (-2)) := by
  rw [initialU_eq_whole_tail hc, initialU_eq_whole_tail hc]
  simp only [advance_add, show (-2 : Int) + 2 = 0 by decide, advance_zero]
  rw [(U w P).T_split p, Bool.xor_comm]

def Block.board (b : Block) (a : Board) : Nat → Board
  | 0 => a
  | n + 1 => flip (b.board a n) (b.pos n)

theorem Block.board_parity (b : Block) (a : Board) (n : Nat) (p : Point) :
    b.board a n p = (a p ^^ bit (b.visits n p)) := by
  induction n with
  | zero => simp [Block.board, Block.visits, bit]
  | succ n ih =>
    rw [Block.board, b.visits_succ]
    by_cases he : b.pos n = p
    · simp only [he, ite_eq_left, flip_same, ih, bit_add, show bit 1 = true from rfl,
        Bool.xor_true]
      cases a p <;> cases bit (b.visits n p) <;> rfl
    · simp [flip, Ne.symm he, he, ih]

def Block.state (b : Block) (a : Board) (n : Nat) : State where
  board := b.board a n
  pos := b.pos n
  dir := (wordTrace b.word (b.start + n)).2

theorem Block.pos_succ (b : Block) (n : Nat) :
    b.pos (n + 1) = move (b.pos n)
      (turn (b.color n) (wordTrace b.word (b.start + n)).2) := by
  have hm (p q : Point) (d : Direction) :
      subPoint (move p d) q = move (subPoint p q) d := by
    cases d <;> apply Prod.ext <;> simp only [move, subPoint] <;> omega
  exact hm _ _ _

theorem Block.state_step {b : Block} {a : Board} {n : Nat}
    (h : b.board a n (b.pos n) = b.color n) :
    step (b.state a n) = b.state a (n + 1) := by
  simp only [step, Block.state, h, Block.board, Block.pos_succ, Block.color,
    Nat.add_succ, wordTrace]
  rfl

theorem Block.run_of_legal {b : Block} {a : Board} (h : b.Legal a)
    {n : Nat} (hn : n ≤ b.length) : run (b.state a 0) n = b.state a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih (by omega)]
    apply Block.state_step
    rw [b.board_parity]
    exact (h n (by omega)).symm

theorem Block.run_of_reads {b : Block} {a : Board}
    (h : ∀ i, i < b.length → readColor (b.state a 0) i = b.color i)
    {n : Nat} (hn : n ≤ b.length) : run (b.state a 0) n = b.state a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hr := ih (by omega)
    rw [run_succ, hr]
    apply Block.state_step
    have hc := h n (by omega)
    unfold readColor at hc
    rw [hr] at hc
    exact hc

/-- Internal legality is equivalent to execution by the repository's actual ant. -/
theorem Block.legal_iff_reads (b : Block) (a : Board) :
    b.Legal a ↔ ∀ i, i < b.length → readColor (b.state a 0) i = b.color i := by
  constructor
  · intro h i hi
    unfold readColor
    rw [Block.run_of_legal h (Nat.le_of_lt hi)]
    change b.board a i (b.pos i) = b.color i
    rw [b.board_parity]
    exact (h i hi).symm
  · intro h i hi
    have hc := h i hi
    rw [readColor, Block.run_of_reads h (Nat.le_of_lt hi)] at hc
    change b.board a i (b.pos i) = b.color i at hc
    rw [b.board_parity] at hc
    exact hc.symm

theorem consistentWord_iff_exists_reads_sharedBoundary {P cut : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    (hc : cut ≤ P) :
    ConsistentWord P w ↔ ∃ aU aV : Board,
      (∀ i, i < cut → readColor ((U w cut).state aU 0) i = w i) ∧
      (∀ i, i < P - cut → readColor ((V w P cut).state aV 0) i = w (cut + i)) ∧
      SharedBoundary w P cut aU aV := by
  simpa only [Block.legal_iff_reads, U_length, V_length, U_color, V_color] using
    (consistentWord_iff_exists_sharedBoundary hdir hd hc)

/-- Both blocks execute consecutively from one board; there is no reset at the cut. -/
theorem boundary_replay {P cut : Nat} {w : Nat → Bool} (hw : ConsistentWord P w)
    (hd : wordDrift P w = (2, -2)) (hc : cut ≤ P) :
    ∀ i, i < P → readColor ((U w cut).state (initialU w P cut) 0) i = w i := by
  have hwhole := ((consistentWord_iff_initial_legal hw.1 hd (Nat.le_refl P)).mp hw).1
  have he : ∀ p, (U w P).Support p → initialU w P P p = initialU w P cut p := by
    intro p _
    rw [initialU_eq_whole_tail (Nat.le_refl P), initialU_eq_whole_tail hc]
  have hlegal := (Block.legal_congr_on_support he).mp hwhole
  intro i hi
  have hread := ((U w P).legal_iff_reads _).mp hlegal i hi
  have hseed : (U w P).state (initialU w P cut) 0 =
      (U w cut).state (initialU w P cut) 0 := rfl
  rw [hseed, U_color] at hread
  exact hread

theorem boundary_after_U {P cut : Nat} {w : Nat → Bool} (hw : ConsistentWord P w)
    (hd : wordDrift P w = (2, -2)) (hc : cut ≤ P) (p : Point) :
    (run ((U w cut).state (initialU w P cut) 0) cut).board (advance p 1) =
      initialV w P cut p := by
  have hu := ((consistentWord_iff_initial_legal hw.1 hd hc).mp hw).1
  rw [Block.run_of_legal hu (Nat.le_refl cut)]
  change (U w cut).board (initialU w P cut) cut (advance p 1) = _
  rw [Block.board_parity, initialV_eq_after_U]
  rfl

/- The counting criterion is valid for every cut. The following geometric
specialization identifies exactly the equal-displacement blocks of round 70.
The direction convention of `wordTrace` is north; the color argument does not
assume a heading at the cut, a first exit, or a minimal period. -/
theorem two_block_displacements {P cut : Nat} {w : Nat → Bool}
    (hc : cut ≤ P) (hd : wordDrift P w = (2, -2))
    (hcut : wordPos w cut = (1, -1)) :
    (U w cut).pos 0 = (0, 0) ∧ (U w cut).pos cut = (1, -1) ∧
      (V w P cut).pos 0 = (0, 0) ∧ (V w P cut).pos (P - cut) = (1, -1) := by
  simp only [U_pos, V_pos, Nat.add_zero, show cut + (P - cut) = P by omega,
    hcut, show wordPos w P = (2, -2) from hd]
  simp [wordPos, wordTrace, advance]

private theorem bit_toNat (n : Nat) : (bit n).toNat = n % 2 := by
  by_cases hn : n % 2 = 1 <;> simp [bit, hn] <;> omega

private theorem bit_eq_xor_iff (m n : Nat) (a : Bool) :
    bit m = (a ^^ bit n) ↔ m % 2 = (a.toNat + n) % 2 := by
  have ha : bit a.toNat = a := by cases a <;> rfl
  have he : (a ^^ bit n) = bit (a.toNat + n) := by rw [bit_add, ha]
  rw [he]
  constructor
  · intro h
    have hh := congrArg Bool.toNat h
    simpa only [bit_toNat] using hh
  · intro h
    simp only [bit, h]

/-- The same two equations with literal natural-number remainders. -/
theorem sharedBoundary_iff_mod_two (w : Nat → Bool) (P cut : Nat) (aU aV : Board) :
    SharedBoundary w P cut aU aV ↔
      (∀ p, (U w cut).Support p →
        (V w P cut).tailCount (advance p 1) % 2 =
          ((aU p).toNat + (U w cut).tailCount (advance p 2)) % 2) ∧
      (∀ p, (V w P cut).Support p →
        (U w cut).tailCount (advance p 1) % 2 =
          ((aV p).toNat + (V w P cut).tailCount (advance p 2)) % 2) := by
  simp only [SharedBoundary, Block.T, bit_eq_xor_iff]

set_option maxRecDepth 8192 in
theorem stdHighwaySE_split_geometry :
    wordPos TwoCellDiagonal.stdHighwaySE 90 = (1, -1) ∧
      (wordTrace TwoCellDiagonal.stdHighwaySE 90).2 = .north := by
  decide +kernel

/-- A positive, genuine two-block instance, with both actual replay and boundary equations. -/
theorem stdHighwaySE_nonvacuity :
    ConsistentWord 104 TwoCellDiagonal.stdHighwaySE ∧
      wordDrift 104 TwoCellDiagonal.stdHighwaySE = (2, -2) ∧
      wordPos TwoCellDiagonal.stdHighwaySE 90 = (1, -1) ∧
      (wordTrace TwoCellDiagonal.stdHighwaySE 90).2 = .north ∧
      (U TwoCellDiagonal.stdHighwaySE 90).Legal
        (initialU TwoCellDiagonal.stdHighwaySE 104 90) ∧
      (V TwoCellDiagonal.stdHighwaySE 104 90).Legal
        (initialV TwoCellDiagonal.stdHighwaySE 104 90) ∧
      SharedBoundary TwoCellDiagonal.stdHighwaySE 104 90
        (initialU TwoCellDiagonal.stdHighwaySE 104 90)
        (initialV TwoCellDiagonal.stdHighwaySE 104 90) := by
  have hw := TwoCellDiagonal.stdHighwaySE_consistent
  have hd := TwoCellDiagonal.stdHighwaySE_drift
  obtain ⟨hu, hv⟩ := (consistentWord_iff_initial_legal hw.1 hd (by decide : 90 ≤ 104)).mp hw
  exact ⟨hw, hd, stdHighwaySE_split_geometry.1, stdHighwaySE_split_geometry.2, hu, hv,
    (consistentWord_iff_sharedBoundary hw.1 hd (by decide) hu hv).mp hw⟩

end LangtonsAnt.PersistA.SharedBoundary
