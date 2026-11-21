import DelayedHighway

namespace LangtonsAnt

/-- A fixed initial perturbation; all generated history remains part of the state. -/
def perturb (mask : Board) (s : State) : State :=
  { board := fun p => s.board p ^^ mask p, pos := s.pos, dir := s.dir }

theorem AgreesBelow.perturb {cut : Int} {s t : State} (h : AgreesBelow cut s t)
    (mask : Board) : AgreesBelow cut (LangtonsAnt.perturb mask s) (LangtonsAnt.perturb mask t) := by
  refine ⟨h.pos, h.dir, ?_⟩
  intro p hp
  change (s.board p ^^ mask p) = (t.board p ^^ mask p)
  rw [h.board p hp]

theorem StandardHighwayFrom.of_agreesBelow {cut : Int} {s t : State} {T : Nat} {v : Point}
    (h : StandardHighwayFrom t T v) (hm : AgreesBelow cut s t)
    (hb : forall n, weight (run t n).pos <= cut) : StandardHighwayFrom s T v := by
  have htrace : forall n,
      (run s n).pos = (run t n).pos ∧ (run s n).dir = (run t n).dir ∧
      readColor s n = readColor t n := by
    intro n
    have hh := hm.run n (fun j _ => hb j)
    refine ⟨hh.pos, hh.dir, ?_⟩
    unfold readColor
    rw [hh.pos]
    exact hh.board _ (hb n)
  refine ⟨?_, ?_⟩
  · intro n hn
    have h0 := htrace n
    have h1 := htrace (n + 104)
    simpa only [h0.1, h0.2.1, h1.1, h1.2.1] using h.1 n hn
  · intro n
    exact (htrace (T + n)).2.2.trans (h.2 n)

theorem flip_xor (board mask : Board) (p : Point) :
    flip (fun q => board q ^^ mask q) p = fun q => flip board p q ^^ mask q := by
  funext q
  by_cases h : q = p
  · subst q
    simp only [flip_same]
    cases board p <;> cases mask p <;> rfl
  · simp [flip, h]

theorem step_perturb_avoids (mask : Board) (s : State) (h : mask s.pos = false) :
    step (perturb mask s) = perturb mask (step s) := by
  simp only [step, perturb, h, Bool.xor_false, flip_xor]

/-- Before first contact the two states differ by exactly the original mask. -/
theorem run_perturb_avoids (mask : Board) (s : State) (n : Nat)
    (h : forall j, j < n -> mask (run s j).pos = false) :
    run (perturb mask s) n = perturb mask (run s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih (fun j hj => h j (by omega)), step_perturb_avoids _ _ (h n (by omega))]
    rfl

def FirstContact (mask : Board) (s : State) (T : Nat) : Prop :=
  mask (run s T).pos = true ∧ forall j, j < T -> mask (run s j).pos = false

theorem FirstContact.unique {mask : Board} {s : State} {T U : Nat}
    (hT : FirstContact mask s T) (hU : FirstContact mask s U) : T = U := by
  by_cases hlt : T < U
  · have hh := hU.2 T hlt
    rw [hT.1] at hh
    contradiction
  · by_cases hgt : U < T
    · have hh := hT.2 U hgt
      rw [hU.1] at hh
      contradiction
    · omega

theorem firstContact_state {mask : Board} {s : State} {T : Nat}
    (h : FirstContact mask s T) :
    run (perturb mask s) T = perturb mask (run s T) :=
  run_perturb_avoids mask s T h.2

theorem firstContact_reads {mask : Board} {s : State} {T : Nat}
    (h : FirstContact mask s T) :
    readColor (perturb mask s) T = !(readColor s T) ∧
    forall j, j < T -> readColor (perturb mask s) j = readColor s j := by
  constructor
  · unfold readColor
    rw [firstContact_state h]
    change ((run s T).board (run s T).pos ^^ mask (run s T).pos) = _
    rw [h.1]
    cases (run s T).board (run s T).pos <;> rfl
  · intro j hj
    unfold readColor
    rw [run_perturb_avoids mask s j (fun i hi => h.2 i (by omega))]
    change ((run s j).board (run s j).pos ^^ mask (run s j).pos) = _
    rw [h.2 j hj, Bool.xor_false]

def opposite : Direction -> Direction
  | .north => .south
  | .east => .west
  | .south => .north
  | .west => .east

theorem turn_not (c : Bool) (d : Direction) : turn (!c) d = opposite (turn c d) := by
  cases c <;> cases d <;> rfl

theorem firstContact_opposite_direction {mask : Board} {s : State} {T : Nat}
    (h : FirstContact mask s T) :
    (run (perturb mask s) (T + 1)).dir = opposite (run s (T + 1)).dir := by
  change turn (readColor (perturb mask s) T) (run (perturb mask s) T).dir = _
  rw [(firstContact_reads h).1, firstContact_state h]
  exact turn_not _ _

/-- Avoiding an initial perturbation forever preserves the entire read and pose trace. -/
theorem perturb_avoids_forever {mask : Board} {s : State}
    (h : forall n, mask (run s n).pos = false) (n : Nat) :
    (run (perturb mask s) n).pos = (run s n).pos ∧
    (run (perturb mask s) n).dir = (run s n).dir ∧
    readColor (perturb mask s) n = readColor s n := by
  have hr := run_perturb_avoids mask s n (fun j _ => h j)
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]
    rfl
  · rw [hr]
    rfl
  · unfold readColor
    rw [hr]
    change ((run s n).board (run s n).pos ^^ mask (run s n).pos) = _
    rw [h n, Bool.xor_false]

theorem perturb_standard_of_avoids {mask : Board} {s : State} {T : Nat} {v : Point}
    (hs : StandardHighwayFrom s T v)
    (h : forall n, mask (run s n).pos = false) :
    StandardHighwayFrom (perturb mask s) T v := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have h0 := perturb_avoids_forever h n
    have h1 := perturb_avoids_forever h (n + 104)
    simpa only [h0.1, h0.2.1, h1.1, h1.2.1] using hs.1 n hn
  · intro n
    exact (perturb_avoids_forever h (T + n)).2.2.trans (hs.2 n)

theorem firstContact_or_never (mask : Board) (s : State) :
    (exists T, FirstContact mask s T) ∨ forall n, mask (run s n).pos = false := by
  classical
  by_cases h : exists n, mask (run s n).pos = true
  · obtain ⟨T, hT, hfirst⟩ := exists_first_nat _ h
    refine Or.inl ⟨T, hT, ?_⟩
    intro j hj
    cases hc : mask (run s j).pos
    · rfl
    · exact False.elim (hfirst j hj hc)
  · right
    intro n
    cases hc : mask (run s n).pos
    · rfl
    · exact False.elim (h ⟨n, hc⟩)

/-- The no-contact case is solved; the contact case retains the full reference history. -/
theorem blank_firstContact_reduction (mask : Board) :
    StandardHighwayFrom (perturb mask blank) 12080 (-2, -2) ∨
    exists T, FirstContact mask blank T ∧
      run (perturb mask blank) T = perturb mask (run blank T) := by
  rcases firstContact_or_never mask blank with ⟨T, hT⟩ | hnever
  · exact Or.inr ⟨T, hT, firstContact_state hT⟩
  · exact Or.inl (perturb_standard_of_avoids blank_standard hnever)

end LangtonsAnt
