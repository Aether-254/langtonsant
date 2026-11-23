import DriftRank

namespace LangtonsAnt.PersistA.GatePath

theorem stable_gap_is_actual_closed_path
    {v : Point} {P i j len : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i < P) (hj : j < P)
    (hc : Drift.SameClass v (wordPos w j) (wordPos w i))
    (ht : Drift.stableTime v P w j = Drift.stableTime v P w i + (len : Int)) :
    let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i len
    p.phase 0 = i ∧ p.phase len = j ∧ p.pos w len = p.pos w 0 := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i len
  have h0 : p.phase 0 = i := by
    simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have hreturn : p.pos w len = p.pos w 0 := by
    apply Drift.path_visit_of_stableTime p hd hj (Nat.le_refl len)
    · simpa only [h0] using hc
    · simpa only [h0] using ht
  have hs := Drift.path_return_stableTime p hd hv hreturn
  have he : p.phase len = j := Drift.stableTime_injective (v := v) (w := w)
    (p.phase_lt len (Nat.le_refl len)) hj (by rw [h0] at hs; omega)
  exact ⟨h0, he, hreturn⟩

theorem two_short_closed_paths
    {v : Point} {P a0 a1 e0 e1 : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ha0 : a0 < P) (ha1 : a1 < P) (he0 : e0 < P) (he1 : e1 < P)
    (hc0 : Drift.SameClass v (wordPos w e0) (wordPos w a0))
    (hc1 : Drift.SameClass v (wordPos w e1) (wordPos w a1))
    (hb0 : Drift.stableTime v P w a1 - Drift.stableTime v P w e0 = 2)
    (hb1 : Drift.stableTime v P w a0 - Drift.stableTime v P w e1 = 2 - (P : Int))
    (ho0 : Drift.stableTime v P w a0 < Drift.stableTime v P w e0)
    (ho1 : Drift.stableTime v P w a1 < Drift.stableTime v P w e1) :
    ∃ d0 d1 : Nat, 0 < d0 ∧ 0 < d1 ∧ d0 < P ∧ d1 < P ∧
      P = d0 + d1 + 4 ∧
      let p0 := ContinuousPhasePath.ofStart (show 0 < P by omega) a0 d0
      let p1 := ContinuousPhasePath.ofStart (show 0 < P by omega) a1 d1
      p0.phase d0 = e0 ∧ p0.pos w d0 = p0.pos w 0 ∧
      p1.phase d1 = e1 ∧ p1.pos w d1 = p1.pos w 0 := by
  let D0 := Drift.stableTime v P w e0 - Drift.stableTime v P w a0
  let D1 := Drift.stableTime v P w e1 - Drift.stableTime v P w a1
  have hD0 : 0 < D0 := by dsimp [D0]; omega
  have hD1 : 0 < D1 := by dsimp [D1]; omega
  have hsum : (P : Int) = D0 + D1 + 4 := by dsimp [D0, D1]; omega
  have hn0 : (D0.toNat : Int) = D0 := Int.toNat_of_nonneg (by omega)
  have hn1 : (D1.toNat : Int) = D1 := Int.toNat_of_nonneg (by omega)
  refine ⟨D0.toNat, D1.toNat, by omega, by omega, by omega, by omega, by omega, ?_⟩
  have hp0 := stable_gap_is_actual_closed_path hd hv ha0 he0 hc0
    (len := D0.toNat) (by rw [hn0]; dsimp [D0]; omega)
  have hp1 := stable_gap_is_actual_closed_path hd hv ha1 he1 hc1
    (len := D1.toNat) (by rw [hn1]; dsimp [D1]; omega)
  exact ⟨hp0.2.1, hp0.2.2, hp1.2.1, hp1.2.2⟩


end LangtonsAnt.PersistA.GatePath
