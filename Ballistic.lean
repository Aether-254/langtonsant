import BoundedMemory

namespace LangtonsAnt

def linearForm (a b : Int) (x : Point) : Int := a * x.1 + b * x.2

/-- Positive rational speed and a nonnegative, uniform bound on backtracking. -/
structure BallisticFrom (s : State) (T : Nat) (a b p q C : Int) : Prop where
  rate_pos : 0 < p
  denominator_pos : 0 < q
  backtrack_nonneg : 0 <= C
  bound : forall n m, T <= n -> n <= m ->
    q * linearForm a b (run s m).pos <=
      q * linearForm a b (run s n).pos - p * ((m : Int) - (n : Int)) + q * C

def Ballistic (s : State) : Prop := exists T a b p q C, BallisticFrom s T a b p q C

theorem BallisticFrom.eventually_below {s : State} {T : Nat} {a b p q C : Int}
    (h : BallisticFrom s T a b p q C) (B : Int) :
    exists U, T <= U ∧ forall m, U <= m -> linearForm a b (run s m).pos < B := by
  let A := q * (linearForm a b (run s T).pos + C - B)
  refine ⟨T + A.toNat + 1, by omega, ?_⟩
  intro m hm
  have hd : 0 <= (m : Int) - (T : Int) := by omega
  have hspeed := Int.mul_le_mul_of_nonneg_right (show 1 <= p from h.rate_pos) hd
  simp only [Int.one_mul] at hspeed
  have hb := h.bound T m (by omega) (by omega)
  have ha : A < (m : Int) - (T : Int) := by omega
  have hmul : q * linearForm a b (run s m).pos < q * B := by
    dsimp [A] at ha
    simp only [Int.mul_sub, Int.mul_add] at ha
    omega
  exact Int.lt_of_mul_lt_mul_left hmul (by have := h.denominator_pos; omega)

/-- The anchor handles the empty list without taking a minimum of an empty set. -/
theorem BallisticFrom.avoids_finite {s : State} {T : Nat} {a b p q C : Int}
    (h : BallisticFrom s T a b p q C) (cells : List Point) :
    exists U, T <= U ∧ forall n, U <= n -> (run s n).pos ∉ cells := by
  let values := 0 :: cells.map (linearForm a b)
  have hne : values ≠ [] := by simp [values]
  obtain ⟨U, hTU, hU⟩ := h.eventually_below (values.min hne)
  refine ⟨U, hTU, ?_⟩
  intro n hn hmem
  have hmin : values.min hne <= linearForm a b (run s n).pos :=
    List.min_le_of_mem (List.mem_cons_of_mem 0 (List.mem_map.mpr ⟨_, hmem, rfl⟩))
  have := hU n hn
  omega

/-- L3: finite initial black support and the pre-ballistic prefix are both left behind. -/
theorem BallisticFrom.boundedMemory {s : State} {T : Nat} {a b p q C : Int}
    (h : BallisticFrom s T a b p q C) (hs : FiniteSupport s.board) :
    exists U, T <= U ∧ BoundedMemoryFrom s U ((q * C / p).toNat + 1) := by
  classical
  obtain ⟨black, hblack⟩ := hs
  let early := (List.range T).map (fun j => (run s j).pos)
  obtain ⟨U, hTU, hU⟩ := h.avoids_finite (black ++ early)
  refine ⟨U, hTU, ?_⟩
  intro n hn
  by_cases hprev : exists j, j < n ∧ (run s j).pos = (run s n).pos
  · obtain ⟨j, hj, he⟩ := hprev
    have hjT : T <= j := by
      apply Classical.byContradiction
      intro hlt
      apply hU n hn
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), he⟩
    have hb := h.bound j n hjT (by omega)
    rw [he] at hb
    have hgap : ((n : Int) - (j : Int)) * p <= q * C := by
      rw [Int.mul_comm]
      omega
    have hdiv := Int.le_ediv_of_mul_le h.rate_pos hgap
    exact Or.inl ⟨j, hj, by omega, he⟩
  · refine Or.inr ⟨?_, ?_⟩
    · intro j hj he
      exact hprev ⟨j, hj, he⟩
    · cases hc : s.board (run s n).pos
      · rfl
      · exact False.elim (hU n hn (List.mem_append_left _ (hblack _ hc)))

theorem Ballistic.boundedMemory {s : State} (h : Ballistic s) (hs : FiniteSupport s.board) :
    EventuallyBoundedMemory s := by
  obtain ⟨T, a, b, p, q, C, h⟩ := h
  obtain ⟨U, _, hU⟩ := h.boundedMemory hs
  exact ⟨U, (q * C / p).toNat + 1, hU⟩

theorem Ballistic.highway {s : State} (h : Ballistic s) (hs : FiniteSupport s.board) :
    exists T P v, 0 < P ∧ v ≠ (0, 0) ∧ HighwayFrom s T P v ∧
      forall n, T <= n -> readColor s (n + P) = readColor s n :=
  (h.boundedMemory hs).highway

theorem unitLinearForm_move_upper (a b : Int) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (x : Point) (d : Direction) :
    linearForm a b (move x d) <= linearForm a b x + 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    cases d <;> simp [linearForm, move] <;> omega

theorem unitLinearForm_run_upper (a b : Int) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (s : State) (k : Nat) :
    linearForm a b (run s k).pos <= linearForm a b s.pos + (k : Int) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := unitLinearForm_move_upper a b ha hb (run s k).pos
      (turn ((run s k).board (run s k).pos) (run s k).dir)
    change linearForm a b (run s (k + 1)).pos <= linearForm a b (run s k).pos + 1 at hm
    omega

/-- A standard diagonal drift gives the explicit speed 4/104 and backtracking bound 108. -/
theorem HighwayFrom.ballisticFrom_of_diagonal {s : State} {T : Nat} {v : Point}
    (h : HighwayFrom s T 104 v) (hv : DiagonalDrift v) :
    exists a b, BallisticFrom s T a b 4 104 108 := by
  have hcoeff : exists a b : Int,
      (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ linearForm a b v = -4 := by
    obtain ⟨hx, hy⟩ := hv
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨-1, -1, Or.inr rfl, Or.inr rfl, by simp [linearForm, hx, hy]⟩
    · exact ⟨-1, 1, Or.inr rfl, Or.inl rfl, by simp [linearForm, hx, hy]⟩
    · exact ⟨1, -1, Or.inl rfl, Or.inr rfl, by simp [linearForm, hx, hy]⟩
    · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by simp [linearForm, hx, hy]⟩
  obtain ⟨a, b, ha, hb, hdrop⟩ := hcoeff
  have hperiod : forall n, T <= n ->
      linearForm a b (run s (n + 104)).pos = linearForm a b (run s n).pos - 4 := by
    intro n hn
    rw [(h n hn).1]
    simp only [linearForm, Int.mul_add] at hdrop ⊢
    omega
  have hblocks : forall n, T <= n -> forall k : Nat,
      linearForm a b (run s (n + 104 * k)).pos =
        linearForm a b (run s n).pos - 4 * (k : Int) := by
    intro n hn k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show n + 104 * (k + 1) = (n + 104 * k) + 104 by omega,
        hperiod _ (by omega), ih]
      omega
  refine ⟨a, b, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩⟩
  intro n m hn hnm
  let k := (m - n) / 104
  let r := (m - n) % 104
  have hr : r < 104 := Nat.mod_lt _ (by decide +kernel)
  have htime : n + 104 * k + r = m := by
    have := Nat.div_add_mod (m - n) 104
    dsimp [k, r]
    omega
  have hrem := unitLinearForm_run_upper a b ha hb (run s (n + 104 * k)) r
  rw [← run_add, htime, hblocks n hn k] at hrem
  omega

theorem EventuallyStandard.ballistic {s : State} (h : EventuallyStandard s) : Ballistic s := by
  obtain ⟨T, v, hv, hhighway, _⟩ := h
  obtain ⟨a, b, hb⟩ := hhighway.ballisticFrom_of_diagonal hv
  exact ⟨T, a, b, 4, 104, 108, hb⟩

/-- A separate, unresolved classification statement, restricted to finite initial support. -/
def PeriodicIsStandard : Prop :=
  forall s : State, FiniteSupport s.board ->
    (exists T P v, 0 < P ∧ HighwayFrom s T P v) -> EventuallyStandard s

theorem highwayConjecture_iff_ballistic_and_periodicIsStandard :
    HighwayConjecture ↔
      (forall s : State, FiniteSupport s.board -> Ballistic s) ∧ PeriodicIsStandard := by
  constructor
  · intro h
    exact ⟨fun s hs => EventuallyStandard.ballistic (h s hs), fun s hs _ => h s hs⟩
  · rintro ⟨hb, hc⟩ s hs
    obtain ⟨T, P, v, hP, _, hh, _⟩ := (hb s hs).highway hs
    exact hc s hs ⟨T, P, v, hP, hh⟩

end LangtonsAnt
