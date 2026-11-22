import BallisticGeneral

/-!
# Leading-edge record pairs of a consistent word

Let `w` be a consistent word of length `P` (`ConsistentWord`, i.e. a white-background periodic
orbit) with drift `v = (a, b)`.  Choose signs `sᵢ = ±1` so that `f = s₁x + s₂y` satisfies
`f v = |a| + |b| > 0`.  A *record* is a time at which `f` exceeds every earlier value.

* `record_pair`: at a record whose arrival heading, turned right, still increases `f` (a *pair
  start*), the next five reads are forced: the cyclic word contains `1 0 0 0 0 1`, the ant closes a
  unit square, and the levels run `L, L+1, L, L-1, L, L-1`.
* Pair starts occur on every other level, consecutive ones are at least 8 steps apart, and one
  period raises the level by `f v`.  Hence `4 (|a| + |b|) ≤ P`
  (`ConsistentWord.four_mul_driftL1_le`), and every consistent word contains the cyclic factor
  `100001` (`ConsistentWord.front_factor`).

All arguments run on the prescribed path of `PeriodicWordRealization` (white board at time `0`,
flipped along the repeated word); its reads agree with the word from time `2P²` on
(`ConsistentWord.prescribed_read`).  These are necessary conditions only.
-/

namespace LangtonsAnt

/-! ## The prescribed board: fresh cells are white, revisits alternate -/

theorem prescribedBoard_fresh {u : Nat -> Bool} {n : Nat}
    (h : forall j, j < n -> wordPos u j ≠ wordPos u n) :
    prescribedBoard u n (wordPos u n) = false := by
  rw [prescribedBoard_parity]
  have he : wordEarlierVisits u n (wordPos u n) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    rw [mem_wordEarlierVisits] at hj
    exact h j hj.1 hj.2
  simp [he]

theorem prescribedBoard_unvisited {u : Nat -> Bool} {p : Point} {a : Nat} :
    forall k, (forall r, a <= r -> r < a + k -> wordPos u r ≠ p) ->
      prescribedBoard u (a + k) p = prescribedBoard u a p := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have hk := h (a + k) (by omega) (by omega)
    rw [show a + (k + 1) = (a + k) + 1 by omega]
    change flip (prescribedBoard u (a + k)) (wordPos u (a + k)) p = _
    rw [flip_other _ (Ne.symm hk)]
    exact ih (fun r h1 h2 => h r h1 (by omega))

theorem prescribedBoard_alternate {u : Nat -> Bool} {s t : Nat} (hst : s < t)
    (heq : wordPos u t = wordPos u s)
    (hgap : forall r, s < r -> r < t -> wordPos u r ≠ wordPos u s) :
    prescribedBoard u t (wordPos u t) = !prescribedBoard u s (wordPos u s) := by
  have h1 : prescribedBoard u (s + 1) (wordPos u s) = !prescribedBoard u s (wordPos u s) := by
    change flip (prescribedBoard u s) (wordPos u s) (wordPos u s) = _
    exact flip_same _ _
  have h2 := prescribedBoard_unvisited (u := u) (p := wordPos u s) (a := s + 1) (t - (s + 1))
    (fun r hr1 hr2 => hgap r (by omega) (by omega))
  rw [show s + 1 + (t - (s + 1)) = t by omega] at h2
  rw [heq, h2, h1]

/-! ## Directions and the gain of a unit step -/

def gain (s1 s2 : Int) : Direction -> Int
  | .north => s2
  | .east => s1
  | .south => -s2
  | .west => -s1

def UnitSign (s : Int) : Prop := s = 1 ∨ s = -1

theorem linearForm_move_gain (s1 s2 : Int) (p : Point) (d : Direction) :
    linearForm s1 s2 (move p d) = linearForm s1 s2 p + gain s1 s2 d := by
  cases d <;> simp only [move, linearForm, gain, Int.mul_add, Int.mul_sub, Int.mul_one] <;> omega

theorem gain_unit {s1 s2 : Int} (h1 : UnitSign s1) (h2 : UnitSign s2) (d : Direction) :
    gain s1 s2 d = 1 ∨ gain s1 s2 d = -1 := by
  unfold UnitSign at h1 h2
  cases d <;> simp only [gain] <;> omega

theorem gain_right_right (s1 s2 : Int) (d : Direction) :
    gain s1 s2 d.right.right = -gain s1 s2 d := by
  cases d <;> simp [gain, Direction.right]

theorem right_four (d : Direction) : d.right.right.right.right = d := by cases d <;> rfl

theorem turn_black_eq (d : Direction) : turn true d = d.right.right.right := by cases d <;> rfl

theorem horizontal_right (d : Direction) : d.right.horizontal = !d.horizontal := by
  cases d <;> rfl

set_option linter.unusedVariables false in
theorem gain_unique {s1 s2 : Int} (h1 : UnitSign s1) (h2 : UnitSign s2) {d e : Direction}
    (hax : d.horizontal = e.horizontal) (hd : gain s1 s2 d = 1) (he : gain s1 s2 e = 1) :
    d = e := by
  unfold UnitSign at h1 h2
  cases d <;> cases e <;> simp [Direction.horizontal, gain] at hax hd he ⊢ <;> omega

theorem move_square (q : Point) (h : Direction) :
    move (move (move (move q h) h.right) h.right.right) h.right.right.right = q := by
  cases h <;> apply Prod.ext <;> simp [move, Direction.right] <;> omega

theorem move_two_ne (p : Point) (h : Direction) :
    move (move p h.right) h.right.right ≠ p := by
  intro he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  cases h <;> simp [move, Direction.right] at h1 h2 <;> omega

/-! ## One step of a word trace -/

theorem wordPos_pred (u : Nat -> Bool) {n : Nat} (hn : 0 < n) :
    wordPos u n = move (wordPos u (n - 1)) (wordTrace u n).2 := by
  cases n with
  | zero => omega
  | succ k => rfl

theorem wordDir_pred (u : Nat -> Bool) {n : Nat} (hn : 0 < n) :
    (wordTrace u n).2 = turn (u (n - 1)) (wordTrace u (n - 1)).2 := by
  cases n with
  | zero => omega
  | succ k => rfl

/-- `n` is a record of `f = s₁x + s₂y` along the word trace. -/
def IsRecord (s1 s2 : Int) (u : Nat -> Bool) (n : Nat) : Prop :=
  forall m, m < n -> linearForm s1 s2 (wordPos u m) < linearForm s1 s2 (wordPos u n)

/-! ## The record-pair gadget -/

/-- At a pair start `m + 1` (a record whose arrival heading turned right still raises `f`), the
reads at `m, …, m+5` are `1 0 0 0 0 1`, the path closes a unit square, and the levels are forced. -/
theorem record_pair {u : Nat -> Bool} {N0 m : Nat} {s1 s2 : Int}
    (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (hread : forall t, N0 <= t -> prescribedBoard u t (wordPos u t) = u t)
    (hm : N0 + 1 <= m) (hrec : IsRecord s1 s2 u (m + 1))
    (hpair : gain s1 s2 (wordTrace u (m + 1)).2.right = 1) :
    u m = true ∧ u (m + 1) = false ∧ u (m + 2) = false ∧ u (m + 3) = false ∧
      u (m + 4) = false ∧ u (m + 5) = true ∧
      wordPos u (m + 4) = wordPos u m ∧ wordPos u (m + 5) = wordPos u (m + 1) ∧
      linearForm s1 s2 (wordPos u (m + 2)) = linearForm s1 s2 (wordPos u (m + 1)) + 1 ∧
      linearForm s1 s2 (wordPos u (m + 3)) = linearForm s1 s2 (wordPos u (m + 1)) ∧
      linearForm s1 s2 (wordPos u (m + 4)) = linearForm s1 s2 (wordPos u (m + 1)) - 1 ∧
      linearForm s1 s2 (wordPos u (m + 6)) = linearForm s1 s2 (wordPos u (m + 1)) - 1 := by
  -- step equations
  have hP1 : wordPos u (m + 1) = move (wordPos u m) (wordTrace u (m + 1)).2 := rfl
  have hD1 : (wordTrace u (m + 1)).2 = turn (u m) (wordTrace u m).2 := rfl
  have hP2 : wordPos u (m + 2) = move (wordPos u (m + 1)) (wordTrace u (m + 2)).2 := rfl
  have hD2 : (wordTrace u (m + 2)).2 = turn (u (m + 1)) (wordTrace u (m + 1)).2 := rfl
  have hP3 : wordPos u (m + 3) = move (wordPos u (m + 2)) (wordTrace u (m + 3)).2 := rfl
  have hD3 : (wordTrace u (m + 3)).2 = turn (u (m + 2)) (wordTrace u (m + 2)).2 := rfl
  have hP4 : wordPos u (m + 4) = move (wordPos u (m + 3)) (wordTrace u (m + 4)).2 := rfl
  have hD4 : (wordTrace u (m + 4)).2 = turn (u (m + 3)) (wordTrace u (m + 3)).2 := rfl
  have hP5 : wordPos u (m + 5) = move (wordPos u (m + 4)) (wordTrace u (m + 5)).2 := rfl
  have hD5 : (wordTrace u (m + 5)).2 = turn (u (m + 4)) (wordTrace u (m + 4)).2 := rfl
  have hP6 : wordPos u (m + 6) = move (wordPos u (m + 5)) (wordTrace u (m + 6)).2 := rfl
  have hD6 : (wordTrace u (m + 6)).2 = turn (u (m + 5)) (wordTrace u (m + 5)).2 := rfl
  -- the arrival heading at `m + 1` raises `f`
  have hf1 := linearForm_move_gain s1 s2 (wordPos u m) (wordTrace u (m + 1)).2
  rw [← hP1] at hf1
  have hr0 := hrec m (by omega)
  have hg1 : gain s1 s2 (wordTrace u (m + 1)).2 = 1 := by
    rcases gain_unit hs1 hs2 (wordTrace u (m + 1)).2 with hg | hg <;> omega
  have hrr := gain_right_right s1 s2 (wordTrace u (m + 1)).2
  have hrrr := gain_right_right s1 s2 (wordTrace u (m + 1)).2.right
  -- time m + 1: fresh, white
  have hu1 : u (m + 1) = false := by
    rw [← hread (m + 1) (by omega)]
    apply prescribedBoard_fresh
    intro j hj he
    have := hrec j hj
    rw [he] at this
    exact Int.lt_irrefl _ this
  have hD2' : (wordTrace u (m + 2)).2 = (wordTrace u (m + 1)).2.right := by rw [hD2, hu1]; rfl
  have hf2 : linearForm s1 s2 (wordPos u (m + 2)) = linearForm s1 s2 (wordPos u (m + 1)) + 1 := by
    rw [hP2, linearForm_move_gain, hD2', hpair]
  -- time m + 2: fresh, white
  have hu2 : u (m + 2) = false := by
    rw [← hread (m + 2) (by omega)]
    apply prescribedBoard_fresh
    intro j hj he
    have hfj := congrArg (linearForm s1 s2) he
    by_cases hj' : j < m + 1
    · have := hrec j hj'; omega
    · have : j = m + 1 := by omega
      subst this; omega
  have hD3' : (wordTrace u (m + 3)).2 = (wordTrace u (m + 1)).2.right.right := by
    rw [hD3, hu2, hD2']; rfl
  have hf3 : linearForm s1 s2 (wordPos u (m + 3)) = linearForm s1 s2 (wordPos u (m + 1)) := by
    rw [hP3, linearForm_move_gain, hD3', hrr, hf2, hg1]; omega
  have hP3' : wordPos u (m + 3) =
      move (move (wordPos u (m + 1)) (wordTrace u (m + 1)).2.right)
        (wordTrace u (m + 1)).2.right.right := by
    rw [hP3, hD3', hP2, hD2']
  -- time m + 3: fresh, white
  have hu3 : u (m + 3) = false := by
    rw [← hread (m + 3) (by omega)]
    apply prescribedBoard_fresh
    intro j hj he
    have hfj := congrArg (linearForm s1 s2) he
    by_cases hj' : j < m + 1
    · have := hrec j hj'; omega
    · by_cases hj2 : j = m + 1
      · subst hj2
        exact move_two_ne _ _ (hP3' ▸ he).symm
      · have : j = m + 2 := by omega
        subst this; omega
  have hD4' : (wordTrace u (m + 4)).2 = (wordTrace u (m + 1)).2.right.right.right := by
    rw [hD4, hu3, hD3']; rfl
  have hP4' : wordPos u (m + 4) = wordPos u m := by
    rw [hP4, hD4', hP3', hP1]
    exact move_square _ _
  have hf4 : linearForm s1 s2 (wordPos u (m + 4)) = linearForm s1 s2 (wordPos u (m + 1)) - 1 := by
    rw [hP4']; omega
  -- time m: the previous read is black
  have hu0 : u m = true := by
    cases hc : u m with
    | true => rfl
    | false =>
      exfalso
      have hpos : 0 < m := by omega
      have hPm := wordPos_pred u hpos
      have hD0 : (wordTrace u (m + 1)).2 = (wordTrace u m).2.right := by rw [hD1, hc]; rfl
      have hback : (wordTrace u m).2 = (wordTrace u (m + 1)).2.right.right.right := by
        rw [hD0, right_four]
      have hfm := linearForm_move_gain s1 s2 (wordPos u (m - 1)) (wordTrace u m).2
      rw [← hPm, hback, hrrr] at hfm
      have hpair' := hpair
      have := hrec (m - 1) (by omega)
      omega
  -- time m + 4: revisit of the cell of time m
  have hu4 : u (m + 4) = false := by
    have hb := prescribedBoard_alternate (u := u) (s := m) (t := m + 4) (by omega) hP4' (by
      intro r hr1 hr2 he
      have hfr := congrArg (linearForm s1 s2) he
      have : r = m + 1 ∨ r = m + 2 ∨ r = m + 3 := by omega
      rcases this with rfl | rfl | rfl <;> omega)
    rw [hread (m + 4) (by omega), hread m (by omega), hu0] at hb
    simpa using hb
  have hD5' : (wordTrace u (m + 5)).2 = (wordTrace u (m + 1)).2 := by
    rw [hD5, hu4, hD4']
    exact right_four _
  have hP5' : wordPos u (m + 5) = wordPos u (m + 1) := by
    rw [hP5, hD5', hP4', hP1]
  -- time m + 5: revisit of the cell of time m + 1
  have hu5 : u (m + 5) = true := by
    have hb := prescribedBoard_alternate (u := u) (s := m + 1) (t := m + 5) (by omega) hP5' (by
      intro r hr1 hr2 he
      have hfr := congrArg (linearForm s1 s2) he
      have : r = m + 2 ∨ r = m + 3 ∨ r = m + 4 := by omega
      rcases this with rfl | rfl | rfl
      · omega
      · exact move_two_ne _ _ (hP3' ▸ he)
      · omega)
    rw [hread (m + 5) (by omega), hread (m + 1) (by omega), hu1] at hb
    simpa using hb
  have hD6' : (wordTrace u (m + 6)).2 = (wordTrace u (m + 1)).2.right.right.right := by
    rw [hD6, hu5, hD5', turn_black_eq]
  have hf6 : linearForm s1 s2 (wordPos u (m + 6)) = linearForm s1 s2 (wordPos u (m + 1)) - 1 := by
    rw [hP6, linearForm_move_gain, hD6', hrrr, hP5', hpair]; omega
  exact ⟨hu0, hu1, hu2, hu3, hu4, hu5, hP4', hP5', hf2, hf3, hf4, hf6⟩

/-! ## Levels along the trace -/

theorem linearForm_wordPos_le {u : Nat -> Bool} {s1 s2 : Int} (hs1 : UnitSign s1)
    (hs2 : UnitSign s2) (a : Nat) :
    forall k, linearForm s1 s2 (wordPos u (a + k)) <= linearForm s1 s2 (wordPos u a) + k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := linearForm_move_gain s1 s2 (wordPos u (a + k)) (wordTrace u (a + k + 1)).2
    have hp : wordPos u (a + (k + 1)) =
        move (wordPos u (a + k)) (wordTrace u (a + k + 1)).2 := rfl
    rw [← hp] at hs
    rcases gain_unit hs1 hs2 (wordTrace u (a + k + 1)).2 with hg | hg <;> omega

theorem linearForm_wordPos_parity {u : Nat -> Bool} {s1 s2 : Int} (hs1 : UnitSign s1)
    (hs2 : UnitSign s2) :
    forall t, (linearForm s1 s2 (wordPos u t) - t) % 2 = 0 := by
  intro t
  induction t with
  | zero => simp [wordPos, wordTrace, linearForm]
  | succ t ih =>
    have hs := linearForm_move_gain s1 s2 (wordPos u t) (wordTrace u (t + 1)).2
    have hp : wordPos u (t + 1) = move (wordPos u t) (wordTrace u (t + 1)).2 := rfl
    rw [← hp] at hs
    rcases gain_unit hs1 hs2 (wordTrace u (t + 1)).2 with hg | hg <;> omega

theorem exists_least {p : Nat -> Prop} :
    forall N t, t < N -> p t -> exists m, p m ∧ forall r, r < m -> ¬ p r := by
  intro N
  induction N with
  | zero => intro t ht; omega
  | succ N ih =>
    intro t ht hp
    by_cases hex : exists r, r < N ∧ p r
    · obtain ⟨r, hr, hpr⟩ := hex
      exact ih r hr hpr
    · refine ⟨t, hp, ?_⟩
      intro r hr hpr
      exact hex ⟨r, by omega, hpr⟩

/-- `t` is the first time the level `f ≥ L` is reached. -/
def FirstReach (s1 s2 : Int) (u : Nat -> Bool) (L : Int) (t : Nat) : Prop :=
  L <= linearForm s1 s2 (wordPos u t) ∧ forall r, r < t -> linearForm s1 s2 (wordPos u r) < L

theorem FirstReach.unique {s1 s2 : Int} {u : Nat -> Bool} {L : Int} {t t' : Nat}
    (h : FirstReach s1 s2 u L t) (h' : FirstReach s1 s2 u L t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with hl | he | hl
  · have := h'.2 t hl; have := h.1; omega
  · exact he
  · have := h.2 t' hl; have := h'.1; omega

/-! ## Periodic traces: first-reach times and the period bound -/

section Periodic

variable {u : Nat -> Bool} {s1 s2 : Int} {N0 P : Nat} {v : Point}

set_option linter.unusedVariables false in
theorem level_unbounded (hs1 : UnitSign s1) (hs2 : UnitSign s2) (hP : 0 < P)
    (hper : forall t, wordPos u (t + P) = addPoint v (wordPos u t))
    (hF : 0 < linearForm s1 s2 v) (L : Int) :
    exists t, L <= linearForm s1 s2 (wordPos u t) := by
  have hblocks : forall k : Nat,
      linearForm s1 s2 (wordPos u (P * k)) = (k : Int) * linearForm s1 s2 v := by
    intro k
    induction k with
    | zero => simp [wordPos, wordTrace, linearForm]
    | succ k ih =>
      rw [show P * (k + 1) = P * k + P by rw [Nat.mul_succ], hper]
      unfold addPoint
      rw [linearForm_add, ih, Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul]
      omega
  refine ⟨P * L.toNat, ?_⟩
  rw [hblocks]
  have h1 : (L.toNat : Int) * linearForm s1 s2 v =
      (L.toNat : Int) + (L.toNat : Int) * (linearForm s1 s2 v - 1) := by
    rw [Int.mul_sub, Int.mul_one]; omega
  have h2 : 0 <= (L.toNat : Int) * (linearForm s1 s2 v - 1) :=
    Int.mul_nonneg (by omega) (by omega)
  omega

theorem firstReach_exists (hs1 : UnitSign s1) (hs2 : UnitSign s2) (hP : 0 < P)
    (hper : forall t, wordPos u (t + P) = addPoint v (wordPos u t))
    (hF : 0 < linearForm s1 s2 v) (L : Int) : exists t, FirstReach s1 s2 u L t := by
  obtain ⟨t, ht⟩ := level_unbounded hs1 hs2 hP hper hF L
  obtain ⟨m, hm, hmin⟩ := exists_least (p := fun t => L <= linearForm s1 s2 (wordPos u t))
    (t + 1) t (by omega) ht
  exact ⟨m, hm, fun r hr => by have := hmin r hr; omega⟩

/-- Basic facts about the first reach of a positive level. -/
theorem FirstReach.props (hs1 : UnitSign s1) (hs2 : UnitSign s2) {L : Int} {t : Nat}
    (h : FirstReach s1 s2 u L t) (hL : 1 <= L) :
    0 < t ∧ linearForm s1 s2 (wordPos u t) = L ∧ gain s1 s2 (wordTrace u t).2 = 1 ∧
      IsRecord s1 s2 u t ∧ L <= (t : Int) := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      have := h.1
      simp [wordPos, wordTrace, linearForm] at this
      omega
    · exact h0
  have hs := linearForm_move_gain s1 s2 (wordPos u (t - 1)) (wordTrace u t).2
  rw [← wordPos_pred u ht] at hs
  have hb := h.2 (t - 1) (by omega)
  have hle := linearForm_wordPos_le (u := u) hs1 hs2 0 t
  simp only [Nat.zero_add] at hle
  have h0 : linearForm s1 s2 (wordPos u 0) = 0 := by simp [wordPos, wordTrace, linearForm]
  have h1 := h.1
  rcases gain_unit hs1 hs2 (wordTrace u t).2 with hg | hg
  · refine ⟨ht, by omega, hg, ?_, by omega⟩
    intro r hr
    have := h.2 r hr
    omega
  · omega

/-- A *pair start* at level `L`: the first reach of `L` turned right still raises `f`. -/
def PairStart (s1 s2 : Int) (u : Nat -> Bool) (L : Int) : Prop :=
  forall t, FirstReach s1 s2 u L t -> gain s1 s2 (wordTrace u t).2.right = 1

theorem firstReach_parity (hs1 : UnitSign s1) (hs2 : UnitSign s2) {L L' : Int} {t t' : Nat}
    (h : FirstReach s1 s2 u L t) (h' : FirstReach s1 s2 u L' t') (hL : 1 <= L) (hL' : 1 <= L')
    (hpar : (L' - L) % 2 = 0) : (wordTrace u t').2.horizontal = (wordTrace u t).2.horizontal := by
  have p := h.props hs1 hs2 hL
  have p' := h'.props hs1 hs2 hL'
  have q := linearForm_wordPos_parity (u := u) hs1 hs2 t
  have q' := linearForm_wordPos_parity (u := u) hs1 hs2 t'
  rw [wordTrace_axis, wordTrace_axis]
  have : t % 2 = t' % 2 := by omega
  rw [this]

theorem firstReach_parity_succ (hs1 : UnitSign s1) (hs2 : UnitSign s2) {L : Int} {t t' : Nat}
    (h : FirstReach s1 s2 u L t) (h' : FirstReach s1 s2 u (L + 1) t') (hL : 1 <= L) :
    (wordTrace u t').2.horizontal = !(wordTrace u t).2.horizontal := by
  have p := h.props hs1 hs2 hL
  have p' := h'.props hs1 hs2 (by omega)
  have q := linearForm_wordPos_parity (u := u) hs1 hs2 t
  have q' := linearForm_wordPos_parity (u := u) hs1 hs2 t'
  rw [wordTrace_axis, wordTrace_axis]
  by_cases ht : t % 2 = 1
  · have : t' % 2 = 0 := by omega
    simp [ht, this]
  · have : t' % 2 = 1 := by omega
    simp [ht, this]

/-- Among two consecutive positive levels at least one is a pair start. -/
theorem pairStart_or_succ (hs1 : UnitSign s1) (hs2 : UnitSign s2) (hP : 0 < P)
    (hper : forall t, wordPos u (t + P) = addPoint v (wordPos u t))
    (hF : 0 < linearForm s1 s2 v) {L : Int} (hL : 1 <= L) :
    PairStart s1 s2 u L ∨ PairStart s1 s2 u (L + 1) := by
  obtain ⟨t, ht⟩ := firstReach_exists hs1 hs2 hP hper hF L
  obtain ⟨t', ht'⟩ := firstReach_exists hs1 hs2 hP hper hF (L + 1)
  rcases gain_unit hs1 hs2 (wordTrace u t).2.right with hg | hg
  · left
    intro r hr
    rw [ht.unique hr] at hg
    exact hg
  · right
    intro r hr
    rw [← ht'.unique hr]
    have p' := ht'.props hs1 hs2 (by omega)
    have hax := firstReach_parity_succ hs1 hs2 ht ht' hL
    have hrrr := gain_right_right s1 s2 (wordTrace u t).2.right
    have hd : (wordTrace u t').2 = (wordTrace u t).2.right.right.right := by
      apply gain_unique hs1 hs2
      · rw [hax, horizontal_right, horizontal_right, horizontal_right]
        cases (wordTrace u t).2.horizontal <;> rfl
      · exact p'.2.2.1
      · omega
    rw [hd, right_four]
    have p := ht.props hs1 hs2 hL
    exact p.2.2.1

set_option linter.unusedVariables false in
/-- A pair start propagates two levels up, at least eight steps later. -/
theorem pairStart_step (hs1 : UnitSign s1) (hs2 : UnitSign s2) (hP : 0 < P)
    (hper : forall t, wordPos u (t + P) = addPoint v (wordPos u t))
    (hF : 0 < linearForm s1 s2 v)
    (hread : forall t, N0 <= t -> prescribedBoard u t (wordPos u t) = u t)
    {L : Int} (hL : (N0 : Int) + 2 <= L) (hps : PairStart s1 s2 u L) {t t2 : Nat}
    (ht : FirstReach s1 s2 u L t) (ht2 : FirstReach s1 s2 u (L + 2) t2) :
    PairStart s1 s2 u (L + 2) ∧ t + 8 <= t2 := by
  have p := ht.props hs1 hs2 (by omega)
  have p2 := ht2.props hs1 hs2 (by omega)
  obtain ⟨m, rfl⟩ : exists m, t = m + 1 := ⟨t - 1, by omega⟩
  have hrp := record_pair hs1 hs2 hread (by omega) p.2.2.2.1 (hps _ ht)
  obtain ⟨_, _, _, _, _, _, _, hP5, hf2, hf3, hf4, hf6⟩ := hrp
  have hf1 := p.2.1
  have hf5 : linearForm s1 s2 (wordPos u (m + 5)) = L := by rw [hP5]; exact hf1
  -- no level `L + 2` up to time `m + 6`
  have hlow : forall r, r <= m + 6 -> linearForm s1 s2 (wordPos u r) <= L + 1 := by
    intro r hr
    by_cases hr1 : r < m + 1
    · have := ht.2 r hr1; omega
    · have : r = m + 1 ∨ r = m + 2 ∨ r = m + 3 ∨ r = m + 4 ∨ r = m + 5 ∨ r = m + 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hgt : m + 6 < t2 := by
    by_cases hc : t2 <= m + 6
    · have := hlow t2 hc; have := ht2.1; omega
    · omega
  have hclimb := linearForm_wordPos_le (u := u) hs1 hs2 (m + 6) (t2 - (m + 6))
  rw [show m + 6 + (t2 - (m + 6)) = t2 by omega] at hclimb
  have ht2l := ht2.1
  refine ⟨?_, by omega⟩
  intro r hr
  rw [← ht2.unique hr]
  have hax := firstReach_parity hs1 hs2 ht ht2 (by omega) (by omega) (by omega)
  have hd : (wordTrace u t2).2 = (wordTrace u (m + 1)).2 :=
    gain_unique hs1 hs2 hax p2.2.2.1 p.2.2.1
  rw [hd]
  exact hps _ ht

/-- One period raises every large first-reach time by exactly `P`. -/
theorem firstReach_period (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (hper : forall t, wordPos u (t + P) = addPoint v (wordPos u t))
    (hF : 0 < linearForm s1 s2 v) {L : Int} (hL : (P : Int) <= L) {t : Nat}
    (ht : FirstReach s1 s2 u L t) :
    FirstReach s1 s2 u (L + linearForm s1 s2 v) (t + P) := by
  have hshift : forall r, linearForm s1 s2 (wordPos u (r + P)) =
      linearForm s1 s2 v + linearForm s1 s2 (wordPos u r) := by
    intro r
    rw [hper]
    unfold addPoint
    exact linearForm_add _ _ _ _
  constructor
  · rw [hshift]; have := ht.1; omega
  · intro r hr
    by_cases hrP : r < P
    · have hle := linearForm_wordPos_le (u := u) hs1 hs2 0 r
      simp only [Nat.zero_add] at hle
      have h0 : linearForm s1 s2 (wordPos u 0) = 0 := by simp [wordPos, wordTrace, linearForm]
      omega
    · have := ht.2 (r - P) (by omega)
      have hs := hshift (r - P)
      rw [show r - P + P = r by omega] at hs
      omega

/-- The core counting argument: `4 f(v) ≤ P`, plus a pair start in the steady regime. -/
theorem pair_count (hs1 : UnitSign s1) (hs2 : UnitSign s2) (hP : 0 < P)
    (hper : forall t, wordPos u (t + P) = addPoint v (wordPos u t))
    (hF : 0 < linearForm s1 s2 v) (heven : linearForm s1 s2 v % 2 = 0)
    (hread : forall t, N0 <= t -> prescribedBoard u t (wordPos u t) = u t) :
    4 * linearForm s1 s2 v <= (P : Int) ∧
      exists m, N0 + 1 <= m ∧ IsRecord s1 s2 u (m + 1) ∧
        gain s1 s2 (wordTrace u (m + 1)).2.right = 1 := by
  have hL1 : (1 : Int) <= ((N0 + P + 2 : Nat) : Int) := by omega
  have hex : exists L0 : Int, ((N0 + P + 2 : Nat) : Int) <= L0 ∧ PairStart s1 s2 u L0 := by
    rcases pairStart_or_succ hs1 hs2 hP hper hF hL1 with h | h
    · exact ⟨_, Int.le_refl _, h⟩
    · exact ⟨_, by omega, h⟩
  obtain ⟨L0, hL0, hps0⟩ := hex
  obtain ⟨t0, ht0⟩ := firstReach_exists hs1 hs2 hP hper hF L0
  -- climb two levels at a time, at least eight steps each
  have hclimb : forall j : Nat, PairStart s1 s2 u (L0 + 2 * (j : Int)) ∧
      forall t, FirstReach s1 s2 u (L0 + 2 * (j : Int)) t -> t0 + 8 * j <= t := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simpa using hps0, ?_⟩
      intro t ht
      have := ht0.unique (by simpa using ht)
      omega
    | succ j ih =>
      obtain ⟨tj, htj⟩ := firstReach_exists hs1 hs2 hP hper hF (L0 + 2 * (j : Int))
      obtain ⟨tn, htn⟩ := firstReach_exists hs1 hs2 hP hper hF (L0 + 2 * (j : Int) + 2)
      have hstep := pairStart_step hs1 hs2 hP hper hF hread (L := L0 + 2 * (j : Int))
        (by omega) ih.1 htj htn
      have hlow := ih.2 tj htj
      have he : L0 + 2 * (((j + 1 : Nat) : Int)) = L0 + 2 * (j : Int) + 2 := by omega
      rw [he]
      refine ⟨hstep.1, ?_⟩
      intro t ht
      have := htn.unique ht
      omega
  obtain ⟨_, hK⟩ := hclimb (linearForm s1 s2 v / 2).toNat
  have hKe : L0 + 2 * (((linearForm s1 s2 v / 2).toNat : Nat) : Int) =
      L0 + linearForm s1 s2 v := by omega
  have hper0 := firstReach_period hs1 hs2 hper hF (L := L0) (by omega) ht0
  rw [← hKe] at hper0
  have hle := hK _ hper0
  have p := ht0.props hs1 hs2 (by omega)
  refine ⟨by omega, t0 - 1, by omega, ?_, ?_⟩
  · rw [show t0 - 1 + 1 = t0 by omega]; exact p.2.2.2.1
  · rw [show t0 - 1 + 1 = t0 by omega]; exact hps0 _ ht0

end Periodic

/-! ## Consequences for consistent words -/

def sgnOne (a : Int) : Int := if 0 <= a then 1 else -1

theorem sgnOne_unit (a : Int) : UnitSign (sgnOne a) := by
  unfold UnitSign sgnOne
  split <;> simp

theorem linearForm_sgnOne (v : Point) :
    linearForm (sgnOne v.1) (sgnOne v.2) v = ((driftL1 v : Nat) : Int) := by
  unfold linearForm driftL1 sgnOne
  split <;> split <;> omega

/-- Every consistent word satisfies the record-pair counting and has a pair start in the regime
where the prescribed board reads the word. -/
theorem ConsistentWord.record_data {P : Nat} {w : Nat -> Bool} (h : ConsistentWord P w)
    (hP : 0 < P) :
    4 * driftL1 (wordDrift P w) <= P ∧
      exists m, P * (2 * P) + 1 <= m ∧
        IsRecord (sgnOne (wordDrift P w).1) (sgnOne (wordDrift P w).2) (repeatWord P w) (m + 1) ∧
        gain (sgnOne (wordDrift P w).1) (sgnOne (wordDrift P w).2)
          (wordTrace (repeatWord P w) (m + 1)).2.right = 1 := by
  have hs1 := sgnOne_unit (wordDrift P w).1
  have hs2 := sgnOne_unit (wordDrift P w).2
  have hper : forall t, wordPos (repeatWord P w) (t + P) =
      addPoint (wordDrift P w) (wordPos (repeatWord P w) t) :=
    fun t => congrArg Prod.fst (repeatWord_trace_period h.1 t)
  have hF0 := linearForm_sgnOne (wordDrift P w)
  have hv := h.2.1
  have hF : 0 < linearForm (sgnOne (wordDrift P w).1) (sgnOne (wordDrift P w).2) (wordDrift P w) := by
    rw [hF0]
    unfold driftL1
    by_cases ha : (wordDrift P w).1 = 0
    · have : (wordDrift P w).2 ≠ 0 := fun hb => hv (Prod.ext ha hb)
      omega
    · omega
  have heven : linearForm (sgnOne (wordDrift P w).1) (sgnOne (wordDrift P w).2)
      (wordDrift P w) % 2 = 0 := by
    have hpar := linearForm_wordPos_parity (u := repeatWord P w) hs1 hs2 P
    have h0 := hper 0
    rw [Nat.zero_add] at h0
    rw [h0] at hpar
    have hz : addPoint (wordDrift P w) (wordPos (repeatWord P w) 0) = wordDrift P w := by
      simp [addPoint, wordPos, wordTrace]
    rw [hz] at hpar
    have := h.even
    omega
  have hread : forall t, P * (2 * P) <= t ->
      prescribedBoard (repeatWord P w) t (wordPos (repeatWord P w) t) = repeatWord P w t :=
    fun t ht => h.prescribed_read hP t ht
  obtain ⟨hcount, m, hm, hrec, hpair⟩ := pair_count hs1 hs2 hP hper hF heven hread
  refine ⟨by omega, m, hm, hrec, hpair⟩

/-- **Period bound.** A consistent word of length `P` with drift `v` has `4 (|v₁| + |v₂|) ≤ P`. -/
theorem ConsistentWord.four_mul_driftL1_le {P : Nat} {w : Nat -> Bool} (h : ConsistentWord P w)
    (hP : 0 < P) : 4 * driftL1 (wordDrift P w) <= P :=
  (h.record_data hP).1

/-- **Front factor.** Every consistent word contains the cyclic factor `1 0 0 0 0 1`. -/
theorem ConsistentWord.front_factor {P : Nat} {w : Nat -> Bool} (h : ConsistentWord P w)
    (hP : 0 < P) :
    exists i, i < P ∧ w i = true ∧ w ((i + 1) % P) = false ∧ w ((i + 2) % P) = false ∧
      w ((i + 3) % P) = false ∧ w ((i + 4) % P) = false ∧ w ((i + 5) % P) = true := by
  obtain ⟨_, m, hm, hrec, hpair⟩ := h.record_data hP
  have hread : forall t, P * (2 * P) <= t ->
      prescribedBoard (repeatWord P w) t (wordPos (repeatWord P w) t) = repeatWord P w t :=
    fun t ht => h.prescribed_read hP t ht
  obtain ⟨h0, h1, h2, h3, h4, h5, _⟩ :=
    record_pair (sgnOne_unit _) (sgnOne_unit _) hread hm hrec hpair
  refine ⟨m % P, Nat.mod_lt _ hP, h0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mod_add_mod]; exact h1
  · rw [Nat.mod_add_mod]; exact h2
  · rw [Nat.mod_add_mod]; exact h3
  · rw [Nat.mod_add_mod]; exact h4
  · rw [Nat.mod_add_mod]; exact h5

/-! ## Consequences for finite-support periodic tails -/

theorem driftL1_rotatePoint (r : Direction) (p : Point) :
    driftL1 (rotatePoint r p) = driftL1 p := by
  cases r <;> simp [rotatePoint, driftL1] <;> omega

/-- **Orbit form.** A finite-support orbit with a periodic tail of period `P` and drift `v` has
`4 (|v₁| + |v₂|) ≤ P`, and its cyclic read word over one period contains `1 0 0 0 0 1`. -/
theorem periodic_tail_record_data {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    4 * driftL1 v <= P ∧
      exists i, i < P ∧ readColor s (T + i) = true ∧
        readColor s (T + (i + 1) % P) = false ∧ readColor s (T + (i + 2) % P) = false ∧
        readColor s (T + (i + 3) % P) = false ∧ readColor s (T + (i + 4) % P) = false ∧
        readColor s (T + (i + 5) % P) = true := by
  have hc := periodic_tail_consistent_at_start hs hP h
  let t := run s T
  let u := normalize t.dir t.pos t
  have ht : HighwayFrom t 0 P v := by
    intro n _
    have hh := h (T + n) (by omega)
    simpa only [t, ← run_add, Nat.add_assoc] using hh
  have hu : HighwayFrom u 0 P (rotatePoint (inverseRotation t.dir) v) :=
    (ht.translate (negPoint t.pos)).rotate (inverseRotation t.dir)
  have hup : u.pos = (0, 0) := by
    have hz : addPoint (negPoint t.pos) t.pos = (0, 0) := by
      apply Prod.ext <;> simp only [addPoint, negPoint] <;> omega
    change rotatePoint (inverseRotation t.dir) (addPoint (negPoint t.pos) t.pos) = _
    rw [hz, rotatePoint_zero]
  have hud : u.dir = .north := by
    change rotateDir (inverseRotation t.dir) t.dir = .north
    have he := rotateDir_inverse t.dir .north
    simpa only [rotateDir_north] using he
  have hr : readColor u = fun i => readColor s (T + i) := by
    funext i
    rw [show readColor u i = readColor t i from normalize_readColor t.dir t.pos t i]
    simp only [t, readColor, run_add]
  have hdrift := hu.word_drift hup hud
  rw [hr] at hdrift
  have hbound := hc.four_mul_driftL1_le hP
  rw [hdrift, driftL1_rotatePoint] at hbound
  obtain ⟨i, hi, h0, h1, h2, h3, h4, h5⟩ := hc.front_factor hP
  exact ⟨hbound, i, hi, h0, h1, h2, h3, h4, h5⟩

end LangtonsAnt
