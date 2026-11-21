import BlankHighway
import Symmetry

namespace LangtonsAnt

/-- Equal reads and equal poses preserve every initial pointwise board agreement. -/
theorem run_coupling {s t : State} (hp : s.pos = t.pos) (hd : s.dir = t.dir)
    (hc : forall n, readColor s n = readColor t n) (n : Nat) :
    (run s n).pos = (run t n).pos ∧ (run s n).dir = (run t n).dir ∧
    forall p, s.board p = t.board p -> (run s n).board p = (run t n).board p := by
  induction n with
  | zero => exact ⟨hp, hd, fun _ h => h⟩
  | succ n ih =>
    have hread : (run s n).board (run s n).pos = (run t n).board (run t n).pos := hc n
    refine ⟨?_, ?_, ?_⟩
    · change move (run s n).pos (turn _ (run s n).dir) = _
      rw [hread, ih.1, ih.2.1]
      rfl
    · change turn _ (run s n).dir = _
      rw [hread, ih.2.1]
      rfl
    · intro p h
      change flip (run s n).board (run s n).pos p = flip (run t n).board (run t n).pos p
      simp only [flip, ih.1, ih.2.2 p h]

def weightFloor : List Point -> Int
  | [] => 0
  | p :: ps => min (weight p) (weightFloor ps)

theorem weightFloor_le {p : Point} {ps : List Point} (h : p ∈ ps) :
    weightFloor ps <= weight p := by
  induction ps with
  | nil => simp at h
  | cons q ps ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · subst p
      exact Int.min_le_left _ _
    · exact Int.le_trans (Int.min_le_right _ _) (ih hmem)

theorem finite_boards_agree_below {s t : State}
    (hs : FiniteSupport s.board) (ht : FiniteSupport t.board) :
    exists b : Int, forall p, weight p < b -> s.board p = t.board p := by
  obtain ⟨cs, hcs⟩ := hs
  obtain ⟨ct, hct⟩ := ht
  refine ⟨weightFloor (cs ++ ct), ?_⟩
  intro p hp
  have hsf : s.board p = false := by
    cases hc : s.board p
    · rfl
    · have hm := weightFloor_le (List.mem_append_left ct (hcs p hc))
      omega
  have htf : t.board p = false := by
    cases hc : t.board p
    · rfl
    · have hm := weightFloor_le (List.mem_append_right cs (hct p hc))
      omega
  exact hsf.trans htf.symm

theorem southwest_offset (k : Nat) :
    offset (-2, -2) k = (-2 * (k : Int), -2 * (k : Int)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change addPoint (offset (-2, -2) k) (-2, -2) = _
    rw [ih]
    apply Prod.ext <;> simp [addPoint] <;> omega

theorem southwest_cofinal (b : Int) : exists k, weight (offset (-2, -2) k) < b := by
  refine ⟨(-b).toNat + 1, ?_⟩
  rw [southwest_offset]
  simp only [weight, Int.natCast_add, Int.natCast_one]
  omega

/-- For finite boards, a standard read trace eventually gives the full half-plane certificate. -/
theorem standard_reads_eventually_match {s : State} (hs : FiniteSupport s.board)
    (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hc : forall n, readColor s n = standardColor n) :
    exists k, AgreesBelow (weight (offset (-2, -2) k)) (run s (104 * k))
      (translate (offset (-2, -2) k) highwaySeed.toState) := by
  have hc' : forall n, readColor s n = readColor highwaySeed.toState n := by
    intro n
    simpa only [Nat.zero_add] using (hc n).trans (highwaySeed_standard.2 n).symm
  have hcouple := run_coupling (t := highwaySeed.toState) hp hd hc'
  obtain ⟨b, hb⟩ := finite_boards_agree_below hs highwaySeed_finite
  obtain ⟨k, hk⟩ := southwest_cofinal b
  refine ⟨k, ?_⟩
  have h0 := hcouple (104 * k)
  have hmatch : AgreesBelow (weight (offset (-2, -2) k))
      (run s (104 * k)) (run highwaySeed.toState (104 * k)) := by
    refine ⟨h0.1, h0.2.1, ?_⟩
    intro p hp
    exact h0.2.2 p (hb p (by omega))
  have hseed := highwaySeed_certificate.blocks k
  exact hmatch.trans (by simpa only [Int.zero_add] using hseed)

theorem standard_reads_highway {s : State}
    (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hc : forall n, readColor s n = standardColor n) :
    StandardHighwayFrom s 0 (-2, -2) := by
  have hc' : forall n, readColor s n = readColor highwaySeed.toState n := by
    intro n
    simpa only [Nat.zero_add] using (hc n).trans (highwaySeed_standard.2 n).symm
  have hcouple := run_coupling (t := highwaySeed.toState) hp hd hc'
  refine ⟨?_, ?_⟩
  · intro n hn
    have h0 := hcouple n
    have h1 := hcouple (n + 104)
    simpa only [h0.1, h0.2.1, h1.1, h1.2.1] using highwaySeed_highway n hn
  · simpa only [Nat.zero_add] using hc

end LangtonsAnt
