import FreshCollision

/-!
# First-visit phases of the standard seed highway

For the seed trajectory `run highwaySeed.toState`, every time is `104*k + φ` with `φ < 104`,
and its position is the in-period position `c_φ` translated by `k*(-2,-2)`.  This file classifies
exactly which phases visit a previously unvisited cell, for every period `k ≥ 2`, relative to the
whole history from time zero.  The finite table is kernel-checked against the real run; the
statement for all `k ≥ 2` follows from the drift and the weight range `[-9, 0]` of one period.
-/

namespace LangtonsAnt

/-- `n` is the first time the trajectory of `s` stands on the cell `(run s n).pos`. -/
def FirstVisitAt (s : State) (n : Nat) : Prop :=
  forall j, j < n -> (run s j).pos ≠ (run s n).pos

/-- Literal positions of one seed period; certified by `cycleTable_check`. -/
def cycleTable : List Point :=
  [(0, 0), (-1, 0), (-1, -1), (-2, -1), (-2, -2), (-3, -2), (-3, -1), (-2, -1), (-2, -2),
   (-1, -2), (-1, -3), (0, -3), (0, -2), (-1, -2), (-1, -3), (-2, -3), (-2, -2), (-1, -2),
   (-1, -3), (0, -3), (0, -4), (-1, -4), (-1, -5), (-2, -5), (-2, -4), (-1, -4), (-1, -5),
   (0, -5), (0, -4), (-1, -4), (-1, -5), (-2, -5), (-2, -6), (-3, -6), (-3, -5), (-2, -5),
   (-2, -6), (-1, -6), (-1, -7), (-2, -7), (-2, -6), (-1, -6), (-1, -5), (-2, -5), (-2, -6),
   (-1, -6), (-1, -7), (0, -7), (0, -8), (-1, -8), (-1, -7), (0, -7), (0, -6), (1, -6),
   (1, -5), (0, -5), (0, -4), (1, -4), (1, -3), (0, -3), (0, -4), (1, -4), (1, -5), (0, -5),
   (0, -6), (1, -6), (1, -7), (0, -7), (0, -6), (1, -6), (1, -5), (0, -5), (0, -4), (1, -4),
   (1, -3), (2, -3), (2, -2), (1, -2), (1, -1), (0, -1), (0, -2), (-1, -2), (-1, -3), (-2, -3),
   (-2, -4), (-1, -4), (-1, -5), (-2, -5), (-2, -4), (-1, -4), (-1, -3), (-2, -3), (-2, -2),
   (-3, -2), (-3, -3), (-4, -3), (-4, -2), (-3, -2), (-3, -3), (-2, -3), (-2, -2), (-1, -2),
   (-1, -3), (-2, -3)]

def cyclePos (j : Nat) : Point := cycleTable.getD j (0, 0)

/-- Walk a finite run and compare each position with a literal list. -/
def checkPosTrace : FiniteState -> List Point -> Bool
  | _, [] => true
  | s, p :: ps => s.pos == p && checkPosTrace s.step ps

theorem FiniteState.run_succ_left (s : FiniteState) (j : Nat) :
    s.run (j + 1) = s.step.run j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (s.run (j + 1)).step = (s.step.run j).step
    rw [ih]

theorem checkPosTrace_sound {s : FiniteState} {ps : List Point}
    (h : checkPosTrace s ps = true) :
    forall j, j < ps.length -> (s.run j).pos = ps.getD j (0, 0) := by
  induction ps generalizing s with
  | nil => intro j hj; simp at hj
  | cons p ps ih =>
    simp only [checkPosTrace, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j =>
      rw [FiniteState.run_succ_left]
      have hh := ih h.2 j (by simp at hj; omega)
      simpa using hh

theorem cycleTable_length : cycleTable.length = 104 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cycleTable_check : checkPosTrace highwaySeed cycleTable = true := by
  decide +kernel

theorem seed_cycle_pos (j : Nat) (hj : j < 104) :
    (run highwaySeed.toState j).pos = cyclePos j := by
  have h := checkPosTrace_sound cycleTable_check j (by rw [cycleTable_length]; exact hj)
  rw [← FiniteState.toState_run]
  exact h

/-- Every seed time `104*q + j` sits at the table position shifted by `q*(-2,-2)`. -/
theorem seed_pos_decomp (q j : Nat) (hj : j < 104) :
    (run highwaySeed.toState (104 * q + j)).pos =
      ((cyclePos j).1 - 2 * (q : Int), (cyclePos j).2 - 2 * (q : Int)) := by
  have hp := (highwaySeed_certificate.block_prefix q j (by omega)).pos
  rw [hp]
  change addPoint (offset (-2, -2) q) (run highwaySeed.toState j).pos = _
  rw [seed_cycle_pos j hj, southwest_offset]
  apply Prod.ext <;> simp only [addPoint] <;> omega

set_option maxRecDepth 100000 in
theorem cycle_weight_check :
    forall j : Fin 104, -9 <= weight (cyclePos j.val) ∧ weight (cyclePos j.val) <= 0 := by
  decide +kernel

/-- Boolean freshness test for periods `k ≥ 2`: no earlier phase of the same period, and no
phase of the previous two periods, lands on the same cell.  Older periods are excluded by
the weight range of one period. -/
def freshCheck (phi : Nat) : Bool :=
  (List.range phi).all (fun psi => cyclePos psi != cyclePos phi) &&
  (List.range 104).all (fun psi =>
    cyclePos psi != ((cyclePos phi).1 - 2, (cyclePos phi).2 - 2) &&
    cyclePos psi != ((cyclePos phi).1 - 4, (cyclePos phi).2 - 4))

/-- The 22 first-visit phases of the standard seed highway. -/
def freshPhases : List Nat :=
  [4, 5, 6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 66, 94, 95, 96]

theorem freshPhases_length : freshPhases.length = 22 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem freshCheck_table :
    forall phi : Fin 104, freshCheck phi.val = decide (phi.val ∈ freshPhases) := by
  decide +kernel

theorem freshCheck_spec (phi : Nat) :
    freshCheck phi = true ↔
      (forall psi, psi < phi -> cyclePos psi ≠ cyclePos phi) ∧
      (forall psi, psi < 104 ->
        cyclePos psi ≠ ((cyclePos phi).1 - 2, (cyclePos phi).2 - 2) ∧
        cyclePos psi ≠ ((cyclePos phi).1 - 4, (cyclePos phi).2 - 4)) := by
  simp only [freshCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]

theorem seed_firstVisit_iff {k phi : Nat} (hk : 2 <= k) (hphi : phi < 104) :
    FirstVisitAt highwaySeed.toState (104 * k + phi) ↔ phi ∈ freshPhases := by
  have hc := freshCheck_table ⟨phi, hphi⟩
  have hmem : phi ∈ freshPhases ↔ freshCheck phi = true := by
    rw [hc]
    simp
  rw [hmem, freshCheck_spec]
  have hpos := seed_pos_decomp k phi hphi
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro psi hpsi he
      have hh := hv (104 * k + psi) (by omega)
      rw [seed_pos_decomp k psi (by omega), hpos, he] at hh
      exact hh rfl
    · intro psi hpsi
      constructor
      · intro he
        have hh := hv (104 * (k - 1) + psi) (by omega)
        rw [seed_pos_decomp (k - 1) psi hpsi, hpos, he] at hh
        apply hh
        apply Prod.ext <;> simp only <;> omega
      · intro he
        have hh := hv (104 * (k - 2) + psi) (by omega)
        rw [seed_pos_decomp (k - 2) psi hpsi, hpos, he] at hh
        apply hh
        apply Prod.ext <;> simp only <;> omega
  · rintro ⟨hA, hB⟩ n hn he
    obtain ⟨q, j, hj, rfl⟩ : exists q j, j < 104 ∧ n = 104 * q + j :=
      ⟨n / 104, n % 104, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 104).symm⟩
    rw [seed_pos_decomp q j hj, hpos] at he
    simp only [Prod.mk.injEq] at he
    have hw := cycle_weight_check ⟨j, hj⟩
    have hw' := cycle_weight_check ⟨phi, hphi⟩
    simp only [weight] at hw hw'
    by_cases h0 : q = k
    · subst h0
      exact hA j (by omega) (Prod.ext (by omega) (by omega))
    · by_cases h1 : q + 1 = k
      · exact (hB j hj).1 (Prod.ext (by simp only; omega) (by simp only; omega))
      · by_cases h2 : q + 2 = k
        · exact (hB j hj).2 (Prod.ext (by simp only; omega) (by simp only; omega))
        · omega

theorem highwaySeed_black_weight : forall p, p ∈ highwaySeed.black -> -5 <= weight p := by
  decide

theorem seed_board_white_of_weight {p : Point} (h : weight p < -5) :
    highwaySeed.toState.board p = false := by
  change decide (p ∈ highwaySeed.black) = false
  rw [decide_eq_false_iff_not]
  intro hm
  have hh := highwaySeed_black_weight p hm
  omega

/-- From period 2 on, every visited cell is white in the seed's initial board. -/
theorem seed_late_cell_white {k phi : Nat} (hk : 2 <= k) (hphi : phi < 104) :
    highwaySeed.toState.board (run highwaySeed.toState (104 * k + phi)).pos = false := by
  apply seed_board_white_of_weight
  rw [seed_pos_decomp k phi hphi]
  have hw := (cycle_weight_check ⟨phi, hphi⟩).2
  simp only [weight] at hw ⊢
  omega

/-- Complete first-visit classification with an explicit threshold. -/
theorem seed_fresh_phase_classification :
    exists K0 : Nat, exists Phi : List Nat,
      forall k, K0 <= k -> forall phi, phi < 104 ->
        (FirstVisitAt highwaySeed.toState (104 * k + phi) ↔ phi ∈ Phi) ∧
        highwaySeed.toState.board (run highwaySeed.toState (104 * k + phi)).pos = false :=
  ⟨2, freshPhases, fun _ hk _ hphi => ⟨seed_firstVisit_iff hk hphi, seed_late_cell_white hk hphi⟩⟩

end LangtonsAnt
