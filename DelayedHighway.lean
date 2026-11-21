import HighwayEntrance

namespace LangtonsAnt

theorem turn_color_injective (d : Direction) {a b : Bool} (h : turn a d = turn b d) : a = b := by
  cases d <;> cases a <;> cases b <;> simp_all [turn, Direction.left, Direction.right]

theorem HighwayFrom.reads_periodic {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) {n : Nat} (hn : T <= n) :
    readColor s (n + P) = readColor s n := by
  have h0 := (h n hn).2
  have h1 := (h (n + 1) (by omega)).2
  have heq : n + 1 + P = (n + P) + 1 := by omega
  rw [heq] at h1
  change turn (readColor s (n + P)) (run s (n + P)).dir =
    turn (readColor s n) (run s n).dir at h1
  rw [h0] at h1
  exact turn_color_injective _ h1

theorem exists_first_nat (P : Nat -> Prop) (h : exists n, P n) :
    exists n, P n ∧ forall j, j < n -> ¬P j := by
  classical
  have aux : forall n, P n -> exists t, P t ∧ forall j, j < t -> ¬P j := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hp : exists j, j < n ∧ P j
      · obtain ⟨j, hj, hP⟩ := hp
        exact ih j hj hP
      · refine ⟨n, hn, ?_⟩
        intro j hj hP
        exact hp ⟨j, hj, hP⟩
  obtain ⟨n, hn⟩ := h
  exact aux n hn

theorem exists_late_first_visit (s : State) (M : Nat) :
    exists p t, M < t ∧ (run s t).pos = p ∧
      forall j, j < t -> (run s j).pos ≠ p := by
  let cells := (List.range (M + 1)).map (fun n => (run s n).pos)
  obtain ⟨m, hm⟩ := escapes_finite_set s cells
  obtain ⟨t, ht, hfirst⟩ := exists_first_nat (fun n => (run s n).pos = (run s m).pos) ⟨m, rfl⟩
  refine ⟨(run s m).pos, t, ?_, ht, hfirst⟩
  have hnot : ¬t <= M := by
    intro hle
    exact hm (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), ht⟩)
  omega

structure AgreesExcept (p : Point) (s t : State) : Prop where
  pos : s.pos = t.pos
  dir : s.dir = t.dir
  board : forall q, q ≠ p -> s.board q = t.board q

theorem AgreesExcept.step {p : Point} {s t : State}
    (h : AgreesExcept p s t) (hp : t.pos ≠ p) :
    AgreesExcept p (LangtonsAnt.step s) (LangtonsAnt.step t) := by
  have hc : s.board s.pos = t.board t.pos := by rw [h.pos]; exact h.board _ hp
  refine ⟨?_, ?_, ?_⟩
  · change move s.pos (turn (s.board s.pos) s.dir) = _
    rw [hc, h.pos, h.dir]
    rfl
  · change turn (s.board s.pos) s.dir = _
    rw [hc, h.dir]
    rfl
  · intro q hq
    change flip s.board s.pos q = flip t.board t.pos q
    simp only [flip, h.pos, h.board q hq]

theorem AgreesExcept.run {p : Point} {s t : State}
    (h : AgreesExcept p s t) (n : Nat)
    (hp : forall j, j < n -> (LangtonsAnt.run t j).pos ≠ p) :
    AgreesExcept p (LangtonsAnt.run s n) (LangtonsAnt.run t n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact (ih (fun j hj => hp j (by omega))).step (hp n (by omega))

theorem board_unchanged_of_avoids (s : State) (p : Point) (n : Nat)
    (h : forall j, j < n -> (run s j).pos ≠ p) : (run s n).board p = s.board p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change flip (run s n).board (run s n).pos p = _
    rw [flip_other _ (Ne.symm (h n (by omega)))]
    exact ih (fun j hj => h j (by omega))

def singleBlack (p : Point) : State :=
  { board := fun q => decide (q = p), pos := (0, 0), dir := .north }

theorem singleBlack_finite (p : Point) : FiniteSupport (singleBlack p).board := by
  refine ⟨[p], ?_⟩
  intro q h
  simpa [singleBlack] using h

theorem singleBlack_first_collision {p : Point} {t : Nat}
    (ht : (run blank t).pos = p)
    (hfirst : forall j, j < t -> (run blank j).pos ≠ p) :
    readColor (singleBlack p) t = true ∧ readColor blank t = false ∧
    forall j, j < t -> readColor (singleBlack p) j = readColor blank j := by
  have hinit : AgreesExcept p (singleBlack p) blank := by
    refine ⟨rfl, rfl, ?_⟩
    intro q hq
    simp [singleBlack, blank, hq]
  have hcouple : forall n, n <= t -> AgreesExcept p (run (singleBlack p) n) (run blank n) := by
    intro n hn
    exact hinit.run n (fun j hj => hfirst j (by omega))
  have hspos : (run (singleBlack p) t).pos = p := (hcouple t (by omega)).pos.trans ht
  have hsboard := board_unchanged_of_avoids (singleBlack p) p t (by
    intro j hj
    rw [(hcouple j (by omega)).pos]
    exact hfirst j hj)
  have hbboard := board_unchanged_of_avoids blank p t hfirst
  refine ⟨?_, ?_, ?_⟩
  · unfold readColor
    rw [hspos, hsboard]
    simp [singleBlack]
  · unfold readColor
    rw [ht, hbboard]
    rfl
  · intro j hj
    unfold readColor
    rw [(hcouple j (by omega)).pos]
    exact (hcouple j (by omega)).board _ (hfirst j hj)

/-- Even one initial black cell admits no uniform time bound for the start of a permanent P104 highway. -/
theorem one_black_unbounded_delay (N : Nat) :
    exists p : Point, forall T, T <= N -> forall v, ¬HighwayFrom (singleBlack p) T 104 v := by
  obtain ⟨p, t, hlate, ht, hfirst⟩ := exists_late_first_visit blank (N + 12184)
  have hcollision := singleBlack_first_collision ht hfirst
  refine ⟨p, ?_⟩
  intro T hT v hhighway
  have hnt : t - 104 + 104 = t := by omega
  have hactual := hhighway.reads_periodic (n := t - 104) (by omega)
  have hblank := blank_highway.reads_periodic (n := t - 104) (by omega)
  rw [hnt] at hactual hblank
  rw [hcollision.1, hcollision.2.2 (t - 104) (by omega)] at hactual
  rw [hcollision.2.1] at hblank
  exact Bool.noConfusion (hactual.trans hblank.symm)

end LangtonsAnt
