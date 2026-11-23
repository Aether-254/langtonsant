import WidthDefects

namespace LangtonsAnt.PersistA.SharedEdge

theorem opposite_colors_share_exactly_one_direction (a b : Direction) (c : Bool)
    (haxis : a.horizontal = b.horizontal) :
    (a = b ∨ turn c a = turn (!c) b) ∧
    ¬ (a = b ∧ turn c a = turn (!c) b) := by
  cases a <;> cases b <;> cases c <;>
    simp_all [Direction.horizontal, turn, Direction.left, Direction.right]

private theorem parity_succ (n : Nat) :
    decide ((n + 1) % 2 = 1) = !(decide (n % 2 = 1)) := by
  by_cases h : n % 2 = 1
  · simp [h, show (n + 1) % 2 ≠ 1 by omega]
  · simp [h, show (n + 1) % 2 = 1 by omega]

theorem consecutive_ranks_share_direction {P i j : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hi : i < P) (hj : j < P)
    (hsc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j))
    (hr : Drift.stableRank P w j = Drift.stableRank P w i + 1) :
    (inDir w i = inDir w j ∨ outDir w i = outDir w j) ∧
    ¬ (inDir w i = inDir w j ∧ outDir w i = outDir w j) := by
  have hc : w j = !(w i) := by
    rw [Drift.consistentWord_stableRank_color hw hj,
      Drift.consistentWord_stableRank_color hw hi, hr]
    exact parity_succ _
  have hl : layer (wordPos w i) = layer (wordPos w j) := by
    obtain ⟨z, hz⟩ := hsc
    rw [hz]
    simp only [layer, weight, addPoint, scalePoint]
    omega
  have ha := same_layer_same_axis w hl
  simpa only [outDir, hc] using
    opposite_colors_share_exactly_one_direction (inDir w i) (inDir w j) (w i) ha

/-- No short-return or one-sidedness assumption is used here. -/
theorem first_return_share_direction {P len : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    (p : ContinuousPhasePath P len) (hlen : 0 < len)
    (hret : p.pos w len = p.pos w 0)
    (hfirst : ∀ r, 0 < r -> r < len -> p.pos w r ≠ p.pos w 0) :
    (inDir w (p.phase 0) = inDir w (p.phase len) ∨
      outDir w (p.phase 0) = outDir w (p.phase len)) ∧
    ¬ (inDir w (p.phase 0) = inDir w (p.phase len) ∧
      outDir w (p.phase 0) = outDir w (p.phase len)) := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0, 0) := by decide
  have hr := Drift.path_firstReturn_rank p hd hv hlen hret hfirst
  have h0 := Drift.path_sameClass_pos p hd 0
  have h1 := Drift.path_sameClass_pos p hd len
  rw [hret] at h1
  exact consecutive_ranks_share_direction hw (p.phase_lt 0 (by omega))
    (p.phase_lt len (by omega)) (h0.trans h1.symm) hr


end LangtonsAnt.PersistA.SharedEdge
