import InfiniteObstacleHighway

namespace LangtonsAnt

def finiteReadWord : FiniteState -> Nat -> List Bool
  | _, 0 => []
  | s, n + 1 => decide (s.pos ∈ s.black) :: finiteReadWord s.step n

theorem finiteReadWord_length (s : FiniteState) (n : Nat) : (finiteReadWord s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [finiteReadWord, List.length_cons, ih]

theorem finiteReadWord_get (s : FiniteState) (n j : Nat) (hj : j < n) :
    (finiteReadWord s n)[j]?.getD false = readColor s.toState j := by
  induction n generalizing s j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [finiteReadWord, List.getElem?_cons_succ]
      rw [ih _ _ (by omega), FiniteState.toState_step]
      change readColor (run s.toState 1) j = readColor s.toState (j + 1)
      simp only [readColor, ← run_add, Nat.add_comm 1 j]

def obstacleWord : Array Bool := (finiteReadWord chainCollisionSeed 548).toArray

def obstacleColor (n : Nat) : Bool := obstacleWord[n % 548]?.getD false

theorem infiniteChain_exact_reads (n : Nat) : readColor infiniteChainSeed n = obstacleColor n := by
  rw [infiniteChain_reads]
  have hj : n % 548 < 548 := Nat.mod_lt _ (by decide)
  have hp := infiniteChain_prefix (n % 548) (by omega)
  have hr : readColor infiniteChainSeed (n % 548) = readColor chainCollisionSeed.toState (n % 548) := by
    unfold readColor
    rw [hp]
    change ((run chainCollisionSeed.toState (n % 548)).board (run chainCollisionSeed.toState (n % 548)).pos ^^
      infiniteChainTail (run chainCollisionSeed.toState (n % 548)).pos) = _
    have ht : infiniteChainTail (run chainCollisionSeed.toState (n % 548)).pos = false := by
      cases hc : infiniteChainTail (run chainCollisionSeed.toState (n % 548)).pos
      · rfl
      · have hw := infiniteChainTail_weight hc
        have hb := (chainCollision_range (n % 548) hj).1
        omega
    rw [ht, Bool.xor_false]
  rw [hr]
  symm
  simpa only [obstacleColor, obstacleWord, List.getElem?_toArray] using finiteReadWord_get chainCollisionSeed 548 (n % 548) hj

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem obstacleWord_no_short_period :
    forall q : Fin 548, 0 < q.val ->
      exists j : Fin 109, obstacleColor (j.val + q.val) ≠ obstacleColor j.val := by
  decide +kernel

theorem infiniteObstacles_exact_reads (n : Nat) :
    readColor infiniteObstacles (12496 + n) = obstacleColor n := by
  rw [infiniteObstacles_reads, infiniteChain_exact_reads]
  simp only [obstacleColor, Nat.mod_mod]

theorem infiniteObstacles_minimal_read_period (q : Nat) (hq : 0 < q) (hsmall : q < 548) :
    ¬(forall n, readColor infiniteObstacles (12496 + n + q) =
      readColor infiniteObstacles (12496 + n)) := by
  intro h
  obtain ⟨j, hj⟩ := obstacleWord_no_short_period ⟨q, hsmall⟩ hq
  have he := h j.val
  rw [Nat.add_assoc, infiniteObstacles_exact_reads, infiniteObstacles_exact_reads] at he
  exact hj he

/-- A shorter period cannot appear later by discarding a finite part of the 548-periodic tail. -/
theorem infiniteObstacles_no_short_tail (T q : Nat) (hq : 0 < q) (hsmall : q < 548) (v : Point) :
    ¬HighwayFrom infiniteObstacles T q v := by
  intro h
  obtain ⟨j, hj⟩ := obstacleWord_no_short_period ⟨q, hsmall⟩ hq
  have he := h.reads_periodic (n := 12496 + (548 * T + j.val)) (by omega)
  rw [Nat.add_assoc, infiniteObstacles_exact_reads, infiniteObstacles_exact_reads] at he
  have hc (x : Nat) : obstacleColor (548 * T + x) = obstacleColor x := by
    unfold obstacleColor
    rw [show (548 * T + x) % 548 = x % 548 by omega]
  rw [show 548 * T + j.val + q = 548 * T + (j.val + q) by omega, hc, hc] at he
  exact hj he

end LangtonsAnt
