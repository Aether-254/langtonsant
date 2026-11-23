import TwoCellDiagonalExtremal

namespace LangtonsAnt.PersistA.ExtremalOverlap

open TwoCellDiagonal

/-- A direct consequence of the existing global extremal-class rigidity. -/
theorem repeated_class_below_top {P i j : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i < P) (hj : j < P) (hne : i ≠ j)
    (hsc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j)) :
    layer (wordPos w i) < topLayer P w := by
  have hle := layer_le_topLayer (w := w) hi
  have hkey := (sameClass_two_negTwo_iff _ _).mp hsc
  by_cases he : layer (wordPos w i) = topLayer P w
  · obtain ⟨_, _, _, _, _, _, huniq, _, _⟩ := topLayer_phase_rigid hw hd hi he
    have heq := huniq j hj (hkey.1.symm.trans he) hkey.2.symm
    exact False.elim (hne heq.symm)
  · omega


theorem other_block_above_repeat {P i j : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (hi : i < P) (hj : j < P) (hne : i ≠ j)
    (hsc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j))
    (A : Nat -> Prop)
    (hbound : ∀ k, k < P -> A k -> layer (wordPos w k) <= layer (wordPos w i)) :
    ∃ k, k < P ∧ ¬ A k ∧ layer (wordPos w i) < layer (wordPos w k) := by
  have hlt := repeated_class_below_top hw hd hi hj hne hsc
  obtain ⟨k, hk, he⟩ := exists_topLayer_phase (w := w) (show 0 < P by omega)
  refine ⟨k, hk, ?_, by omega⟩
  intro ha
  have hb := hbound k hk ha
  omega


end LangtonsAnt.PersistA.ExtremalOverlap
