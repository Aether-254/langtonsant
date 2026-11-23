import WidthDefects

namespace LangtonsAnt.PersistA.BlockReturn

theorem short_clock_gap {P i j k l : Int}
    (hi0 : 0 <= i) (hiP : i < P) (hj0 : 0 <= j) (hjP : j < P)
    (hpos : 0 < (j - P * l) - (i - P * k))
    (hshort : (j - P * l) - (i - P * k) < P) :
    (k = l ∧ i < j) ∨ (k = l + 1 ∧ j < i) := by
  have hP : 0 <= P := by omega
  have hlk : l <= k := by
    apply Classical.byContradiction
    intro hn
    have hm := Int.mul_le_mul_of_nonneg_left (show k + 1 <= l by omega) hP
    rw [Int.mul_add, Int.mul_one] at hm
    omega
  have hkl : k <= l + 1 := by
    apply Classical.byContradiction
    intro hn
    have hm := Int.mul_le_mul_of_nonneg_left (show l + 2 <= k by omega) hP
    rw [Int.mul_add] at hm
    omega
  by_cases he : k = l
  · subst k
    exact Or.inl ⟨rfl, by omega⟩
  · have he' : k = l + 1 := by omega
    rw [he', Int.mul_add, Int.mul_one] at hshort
    exact Or.inr ⟨he', by omega⟩

theorem short_forward_cross_block {P cut i j k l r x y : Int}
    (hi0 : 0 <= i) (hic : i < cut) (hcj : cut <= j) (hjP : j < P)
    (hx : x = 2 * k + r) (hy : y = 2 * l + r - 1)
    (hpos : 0 < (j - P * l) - (i - P * k))
    (hshort : (j - P * l) - (i - P * k) < P) : x = y + 1 := by
  rcases short_clock_gap hi0 (by omega) (by omega) hjP hpos hshort with h | h
  · omega
  · omega

theorem short_reverse_cross_block {P cut i j k l r x y : Int}
    (hi0 : 0 <= i) (hic : i < cut) (hcj : cut <= j) (hjP : j < P)
    (hx : x = 2 * k + r) (hy : y = 2 * l + r - 1)
    (hpos : 0 < (i - P * k) - (j - P * l))
    (hshort : (i - P * k) - (j - P * l) < P) : y = x + 1 := by
  rcases short_clock_gap (by omega) hjP hi0 (by omega) hpos hshort with h | h
  · omega
  · omega

/-- A genuine short physical return admits exactly the two possible carries. -/
theorem short_return_lift {v : Point} {P len : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hpos : 0 < len) (hshort : len < P) (hret : p.pos w len = p.pos w 0) :
    (Drift.lift v (wordPos w (p.phase 0)) = Drift.lift v (wordPos w (p.phase len)) ∧
      p.phase 0 < p.phase len) ∨
    (Drift.lift v (wordPos w (p.phase 0)) = Drift.lift v (wordPos w (p.phase len)) + 1 ∧
      p.phase len < p.phase 0) := by
  have ht := Drift.path_return_stableTime p hd hv hret
  simp only [Drift.stableTime] at ht
  have hi := p.phase_lt 0 (by omega)
  have hj := p.phase_lt len (by omega)
  have result := short_clock_gap (P := (P : Int))
    (i := (p.phase 0 : Int)) (j := (p.phase len : Int))
    (k := Drift.lift v (wordPos w (p.phase 0)))
    (l := Drift.lift v (wordPos w (p.phase len)))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rcases result with h | h
  · exact Or.inl ⟨h.1, by omega⟩
  · exact Or.inr ⟨h.1, by omega⟩

theorem upper_run_return_lift {P i len : Nat} {w : Nat -> Bool} {t : Int}
    (r : WidthDefects.UpperRun P w t i len) (hP : 0 < P)
    (hd : wordDrift P w = (2, -2))
    (hret : (ContinuousPhasePath.ofStart hP i len).pos w len =
      (ContinuousPhasePath.ofStart hP i len).pos w 0) :
    let p := ContinuousPhasePath.ofStart hP i len
    (Drift.lift (2, -2) (wordPos w (p.phase 0)) =
        Drift.lift (2, -2) (wordPos w (p.phase len)) ∧ p.phase 0 < p.phase len) ∨
    (Drift.lift (2, -2) (wordPos w (p.phase 0)) =
        Drift.lift (2, -2) (wordPos w (p.phase len)) + 1 ∧ p.phase len < p.phase 0) := by
  exact short_return_lift (ContinuousPhasePath.ofStart hP i len) hd
    (by decide) r.length_pos (r.physical_return_short hP hd hret) hret


end LangtonsAnt.PersistA.BlockReturn
