import InfiniteObstacleHighway

namespace LangtonsAnt

/-- Agreement on the reference's initially colored cells suffices for a finite trace. -/
theorem finite_run_coupling {s t : State} (hp : s.pos = t.pos) (hd : s.dir = t.dir) (n : Nat)
    (hb : forall j, j < n -> s.board (run t j).pos = t.board (run t j).pos) :
    (run s n).pos = (run t n).pos ∧ (run s n).dir = (run t n).dir ∧
    forall p, s.board p = t.board p -> (run s n).board p = (run t n).board p := by
  induction n with
  | zero => exact ⟨hp, hd, fun _ h => h⟩
  | succ n ih =>
    have hh := ih (fun j hj => hb j (by omega))
    have hc : (run s n).board (run s n).pos = (run t n).board (run t n).pos := by
      rw [hh.1]
      exact hh.2.2 _ (hb n (by omega))
    refine ⟨?_, ?_, ?_⟩
    · change move (run s n).pos (turn _ (run s n).dir) = _
      rw [hc, hh.1, hh.2.1]
      rfl
    · change turn _ (run s n).dir = _
      rw [hc, hh.2.1]
      rfl
    · intro p he
      change flip (run s n).board (run s n).pos p = flip (run t n).board (run t n).pos p
      simp only [flip, hh.1, hh.2.2 p he]

theorem run_x_lower_bound (s : State) (n : Nat) : s.pos.1 - (n : Int) <= (run s n).pos.1 := by
  have hm (p : Point) (d : Direction) : p.1 - 1 <= (move p d).1 := by
    cases d <;> simp [move] <;> omega
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := hm (run s n).pos (turn (readColor s n) (run s n).dir)
    change s.pos.1 - ((n + 1 : Nat) : Int) <= (move (run s n).pos (turn (readColor s n) (run s n).dir)).1
    omega

theorem finite_infinite_board_agreement (N n : Nat) (hn : N <= n) (p : Point)
    (hp : -(N : Int) <= p.1) : (multipleObstacles n).board p = infiniteObstacles.board p := by
  have he : (multipleObstacles n).board p = true ↔ infiniteObstacles.board p = true := by
    rw [multipleObstacles_black, infiniteObstacles_black]
    constructor
    · rintro ⟨i, _, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_, hi⟩
      rw [hi] at hp
      omega
  cases hf : (multipleObstacles n).board p <;> cases hi : infiniteObstacles.board p <;> simp_all

/-- Every fixed observation horizon is identical once enough obstacles are retained. -/
theorem finiteChains_match_infinite_prefix (N n : Nat) (hn : N <= n) :
    forall j, j <= N ->
      (run (multipleObstacles n) j).pos = (run infiniteObstacles j).pos ∧
      (run (multipleObstacles n) j).dir = (run infiniteObstacles j).dir ∧
      readColor (multipleObstacles n) j = readColor infiniteObstacles j := by
  have hb (j : Nat) (hj : j <= N) :
      (multipleObstacles n).board (run infiniteObstacles j).pos =
        infiniteObstacles.board (run infiniteObstacles j).pos := by
    apply finite_infinite_board_agreement N n hn
    have hw := run_x_lower_bound infiniteObstacles j
    change (0 : Int) - (j : Int) <= (run infiniteObstacles j).pos.1 at hw
    omega
  intro j hj
  have hc := finite_run_coupling (s := multipleObstacles n) (t := infiniteObstacles)
    rfl rfl j (fun m hm => hb m (by omega))
  refine ⟨hc.1, hc.2.1, ?_⟩
  unfold readColor
  rw [hc.1]
  exact hc.2.2 _ (hb j hj)

/-- Eventual standard behavior is not preserved by agreement on every finite trace prefix. -/
theorem finiteChains_standard_infiniteChain_nonstandard :
    (forall n : Nat, FiniteSupport (multipleObstacles n).board ∧ EventuallyStandard (multipleObstacles n)) ∧
    ¬FiniteSupport infiniteObstacles.board ∧ ¬EventuallyStandard infiniteObstacles := by
  refine ⟨?_, infiniteObstacles_not_finite, infiniteObstacles_not_eventuallyStandard⟩
  intro n
  exact ⟨multipleObstacles_finite n,
    ⟨12496 + 548 * n, (-2, -2), diagonal_rotated_southwest .north, multipleObstacles_standard n⟩⟩

end LangtonsAnt
