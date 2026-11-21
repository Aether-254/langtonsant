import SingleBlackCoverCells
import Phase49Blank

/-!
# Every single black cell leads to the standard highway

For any initial state with exactly one black cell, any ant position and any heading, the ant
eventually runs the standard 104-step highway.

Proof, for the ant at the origin facing north (the general case follows by symmetry):
* if the blank orbit never visits the black cell, the run is the blank run;
* if it first visits the cell before time 13952, the cell is one of the 2215 cells of
  `earlyCells` (checked by walking the blank orbit), each with a kernel-checked certificate;
* otherwise `singleBlack_late_all` applies (all 22 first-visit phases, including phase 49).
-/

namespace LangtonsAnt

/-- Blank board, one black cell `q`, ant at the origin facing north. -/
theorem singleBlack_standard (q : Point) : EventuallyStandard (singleBlack q) := by
  rcases firstContact_or_never (fun x => decide (x = q)) blank with ⟨tau, htau⟩ | hnever
  · by_cases hlate : 13952 <= tau
    · exact singleBlack_late_all htau hlate
    · have hq : (run blank tau).pos = q := by simpa using htau.1
      have hmem := earlyCells_cover tau (by omega)
      rw [hq] at hmem
      exact earlyCells_ok q hmem
  · rw [singleBlack_eq_perturb]
    exact ⟨12080, (-2, -2), diagonal_rotated_southwest .north,
      perturb_standard_of_avoids blank_standard hnever⟩

/-- Blank board, one black cell `q`, ant at `p` with heading `d`. -/
def singleBlackAt (p : Point) (d : Direction) (q : Point) : State :=
  { board := fun x => decide (x = q), pos := p, dir := d }

theorem singleBlackAt_eq_pose (p : Point) (d : Direction) (q : Point) :
    singleBlackAt p d q =
      pose d p (singleBlack (rotatePoint (inverseRotation d) (subPoint q p))) := by
  have hext : forall s t : State, s.board = t.board -> s.pos = t.pos -> s.dir = t.dir -> s = t := by
    intro s t h1 h2 h3
    cases s; cases t
    simp only at h1 h2 h3
    subst h1; subst h2; subst h3
    rfl
  apply hext
  · funext x
    simp only [singleBlackAt, pose, LangtonsAnt.translate, rotateState, singleBlack]
    have hiff : (rotatePoint (inverseRotation d) (subPoint x p) =
        rotatePoint (inverseRotation d) (subPoint q p)) ↔ x = q := by
      constructor
      · intro h
        have h2 := congrArg (rotatePoint d) h
        rw [inverse_rotatePoint, inverse_rotatePoint] at h2
        apply Prod.ext <;> simp only [subPoint, Prod.mk.injEq] at h2 <;> omega
      · intro h; rw [h]
    exact decide_eq_decide.mpr hiff.symm
  · simp only [singleBlackAt, pose, LangtonsAnt.translate, rotateState, singleBlack, rotatePoint_zero]
    apply Prod.ext <;> simp [addPoint]
  · simp only [singleBlackAt, pose, LangtonsAnt.translate, rotateState, singleBlack]
    cases d <;> rfl

/-- **Single black cell theorem.**  For every ant position `p`, heading `d` and black cell `q`
on an otherwise white board, the ant eventually runs the standard highway. -/
theorem singleBlackAt_standard (p : Point) (d : Direction) (q : Point) :
    EventuallyStandard (singleBlackAt p d q) := by
  rw [singleBlackAt_eq_pose]
  exact (singleBlack_standard _).pose d p

end LangtonsAnt
