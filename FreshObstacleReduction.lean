import SingleFlipReduction

namespace LangtonsAnt

/-- Only white-to-black initial perturbations are needed for the finite-support induction. -/
def AddBlackStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall q, s.board q = false -> EventuallyStandard (flipCell s q)

/-- The collision may occur during the transient; it need not follow a highway entry. -/
def FreshObstacleStability : Prop :=
  forall s : State, FiniteSupport s.board -> EventuallyStandard s ->
    forall T, s.board (run s T).pos = false ->
      (forall j, j < T -> (run s j).pos ≠ (run s T).pos) ->
      EventuallyStandard (flipCell (run s T) (run s T).pos)

theorem addBlackStability_implies_highway (h : AddBlackStability) : HighwayConjecture := by
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
        apply h _ (FiniteState.finiteSupport ⟨cells, p, d⟩) (ih p d) q
        simp [FiniteState.toState, hq]
  intro s hs
  obtain ⟨f, hf⟩ := finiteSupport_representable s hs
  have hh := hlist f.black f.pos f.dir
  change EventuallyStandard f.toState at hh
  rw [hf] at hh
  exact hh

theorem highwayConjecture_iff_addBlackStability : HighwayConjecture ↔ AddBlackStability := by
  constructor
  · intro h s hs _ q _
    exact h _ (finiteSupport_flipCell hs q)
  · exact addBlackStability_implies_highway

theorem freshObstacle_implies_addBlack (h : FreshObstacleStability) : AddBlackStability := by
  intro s hs hst q hq
  rw [flipCell_eq_perturb]
  rcases firstContact_or_never (fun x => decide (x = q)) s with ⟨T, hT⟩ | hnever
  · apply EventuallyStandard.of_run (n := T)
    rw [firstContact_state hT]
    have hp : (run s T).pos = q := by simpa using hT.1
    have hfresh : forall j, j < T -> (run s j).pos ≠ (run s T).pos := by
      intro j hj
      rw [hp]
      simpa using hT.2 j hj
    have hh := h s hs hst T (by rw [hp]; exact hq) hfresh
    rw [hp, flipCell_eq_perturb] at hh
    exact hh
  · obtain ⟨T, v, hv, hstd⟩ := hst
    exact ⟨T, v, hv, perturb_standard_of_avoids hstd hnever⟩

theorem highwayConjecture_iff_freshObstacleStability :
    HighwayConjecture ↔ FreshObstacleStability := by
  constructor
  · intro h s hs _ T _ _
    exact h _ (finiteSupport_flipCell (finiteSupport_run s hs T) _)
  · intro h
    exact addBlackStability_implies_highway (freshObstacle_implies_addBlack h)

end LangtonsAnt
