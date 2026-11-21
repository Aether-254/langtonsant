import EntranceChecker
import FirstContact

namespace LangtonsAnt

def flipCell (s : State) (p : Point) : State :=
  { s with board := flip s.board p }

theorem flipCell_eq_perturb (s : State) (p : Point) :
    flipCell s p = perturb (fun q => decide (q = p)) s := by
  have hb : flip s.board p = fun q => s.board q ^^ decide (q = p) := by
    funext q
    by_cases h : q = p
    · subst q
      simp only [flip_same, decide_true]
      cases s.board p <;> rfl
    · simp [flip, h]
  simp only [flipCell, perturb, hb]

theorem finiteSupport_flipCell {s : State} (h : FiniteSupport s.board) (p : Point) :
    FiniteSupport (flipCell s p).board := finiteSupport_flip h p

theorem standardColor_add_periods (k n : Nat) : standardColor (104 * k + n) = standardColor n := by
  rw [standardColor_eq_certifiedColor, standardColor_eq_certifiedColor]
  simp [certifiedColor, Nat.add_mod]

theorem StandardHighwayFrom.shift_periods {s : State} {T : Nat} {v : Point}
    (h : StandardHighwayFrom s T v) (k : Nat) : StandardHighwayFrom s (T + 104 * k) v := by
  refine ⟨fun n hn => h.1 n (by omega), ?_⟩
  intro n
  rw [Nat.add_assoc, h.2, standardColor_add_periods]

theorem StandardHighwayFrom.of_run {s : State} {n T : Nat} {v : Point}
    (h : StandardHighwayFrom (run s n) T v) : StandardHighwayFrom s (n + T) v := by
  refine ⟨?_, ?_⟩
  · intro j hj
    have hh := h.1 (j - n) (by omega)
    simp only [← run_add] at hh
    have h0 : n + (j - n) = j := by omega
    have h1 : n + (j - n + 104) = j + 104 := by omega
    simpa only [h0, h1] using hh
  · intro j
    have hh := h.2 j
    simpa only [readColor, ← run_add, Nat.add_assoc] using hh

theorem EventuallyStandard.of_run {s : State} {n : Nat}
    (h : EventuallyStandard (run s n)) : EventuallyStandard s := by
  obtain ⟨T, v, hv, hT⟩ := h
  exact ⟨n + T, v, hv, hT.of_run⟩

theorem EventuallyStandard.run {s : State} (h : EventuallyStandard s) (n : Nat) :
    EventuallyStandard (LangtonsAnt.run s n) := by
  obtain ⟨T, v, hv, hT⟩ := h
  have hlate := hT.shift_periods n
  let U := T + 104 * n - n
  have hU : n + U = T + 104 * n := by dsimp [U]; omega
  refine ⟨U, v, hv, ?_, ?_⟩
  · intro j hj
    have hh := hlate.1 (n + j) (by omega)
    simpa only [← run_add, Nat.add_assoc] using hh
  · intro j
    have hh := hlate.2 j
    simpa only [readColor, ← run_add, ← hU, Nat.add_assoc] using hh

theorem EventuallyStandard.pose {s : State} (h : EventuallyStandard s)
    (r : Direction) (origin : Point) : EventuallyStandard (pose r origin s) := by
  obtain ⟨T, v, hv, hT⟩ := h
  have hv' : DiagonalDrift (rotatePoint r v) := by
    cases r <;> simp [DiagonalDrift, rotatePoint] at hv ⊢ <;> omega
  exact ⟨T, rotatePoint r v, hv', (hT.rotate r).translate origin⟩

def whiteAt (p : Point) (d : Direction) : State :=
  { board := fun _ => false, pos := p, dir := d }

theorem whiteAt_standard (p : Point) (d : Direction) :
    StandardHighwayFrom (whiteAt p d) 12080 (rotatePoint d (-2, -2)) := by
  have h := (blank_standard.rotate d).translate p
  have heq : pose d p blank = whiteAt p d := by
    simp [pose, rotateState, translate, blank, whiteAt]
  change StandardHighwayFrom (pose d p blank) 12080 _ at h
  rw [heq] at h
  exact h

/-- The remaining local stability assertion; deliberately left as an unproved proposition. -/
def CurrentCellFlipStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    EventuallyStandard (flipCell s s.pos)

def ArbitraryCellFlipStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall p, EventuallyStandard (flipCell s p)

theorem currentCellFlipStability_implies_arbitrary
    (h : CurrentCellFlipStability) : ArbitraryCellFlipStability := by
  intro s hs hstandard p
  rw [flipCell_eq_perturb]
  rcases firstContact_or_never (fun q => decide (q = p)) s with ⟨T, hT⟩ | hnever
  · apply EventuallyStandard.of_run (n := T)
    rw [firstContact_state hT]
    have hp : (run s T).pos = p := by simpa using hT.1
    have hh := h (run s T) (finiteSupport_run s hs T) (hstandard.run T)
    rw [hp, flipCell_eq_perturb] at hh
    exact hh
  · obtain ⟨T, v, hv, hstandard⟩ := hstandard
    exact ⟨T, v, hv, perturb_standard_of_avoids hstandard hnever⟩

def stateOfCells (cells : List Point) (p : Point) (d : Direction) : State :=
  ({ black := cells, pos := p, dir := d } : FiniteState).toState

theorem arbitraryCellFlipStability_implies_highway
    (h : ArbitraryCellFlipStability) : HighwayConjecture := by
  have hlist : forall cells p d, EventuallyStandard (stateOfCells cells p d) := by
    intro cells
    induction cells with
    | nil =>
      intro p d
      exact ⟨12080, rotatePoint d (-2, -2), diagonal_rotated_southwest d, whiteAt_standard p d⟩
    | cons q cells ih =>
      intro p d
      by_cases hq : q ∈ cells
      · have heq : stateOfCells (q :: cells) p d = stateOfCells cells p d := by
          have hb : (fun x => decide (x ∈ q :: cells)) = fun x => decide (x ∈ cells) := by
            funext x
            by_cases hx : x = q <;> simp [hx, hq]
          simp only [stateOfCells, FiniteState.toState, hb]
        rw [heq]
        exact ih p d
      · have heq : stateOfCells (q :: cells) p d = flipCell (stateOfCells cells p d) q := by
          have hb : (fun x => decide (x ∈ q :: cells)) = flip (fun x => decide (x ∈ cells)) q := by
            funext x
            by_cases hx : x = q <;> simp [flip, hx, hq]
          simp only [stateOfCells, FiniteState.toState, flipCell, hb]
        rw [heq]
        exact h _ (FiniteState.finiteSupport ⟨cells, p, d⟩) (ih p d) q
  intro s hs
  obtain ⟨f, hf⟩ := finiteSupport_representable s hs
  have hh := hlist f.black f.pos f.dir
  change EventuallyStandard f.toState at hh
  rw [hf] at hh
  exact hh

theorem highwayConjecture_iff_currentCellFlipStability :
    HighwayConjecture ↔ CurrentCellFlipStability := by
  constructor
  · intro h s hs _
    exact h _ (finiteSupport_flipCell hs s.pos)
  · intro h
    exact arbitraryCellFlipStability_implies_highway (currentCellFlipStability_implies_arbitrary h)

theorem FiniteState.toState_flip (s : FiniteState) (p : Point) :
    ({ s with black := toggleCells s.black p } : FiniteState).toState = flipCell s.toState p := by
  have hb : (fun q => decide (q ∈ toggleCells s.black p)) =
      flip (fun q => decide (q ∈ s.black)) p := by
    funext q
    exact toggleCells_board _ _ _
  simp only [FiniteState.toState, flipCell, hb]

end LangtonsAnt
