import SpacedHighwayWord

namespace LangtonsAnt

theorem spacedColor_common_collision (k n : Nat) (hn : n < 548) :
    spacedColor k n = obstacleColor n := by
  have hP : n < spacedPeriod k := by unfold spacedPeriod; omega
  simp only [spacedColor, Nat.mod_eq_of_lt hP, ite_eq_left hn]

theorem spacedColor_common_prefix (k n : Nat) (hk : 0 < k) (hn : n < 652) :
    spacedColor k n = spacedColor 1 n := by
  have hP : n < spacedPeriod k := by unfold spacedPeriod; omega
  simp only [spacedColor, Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt (show n < spacedPeriod 1 from hn)]

theorem spacedColor_standard (k n : Nat) (hlo : 548 <= n) (hhi : n < spacedPeriod k) :
    spacedColor k n = certifiedColor (n - 548) := by
  simp only [spacedColor, Nat.mod_eq_of_lt hhi, ite_eq_right (show ¬n < 548 by omega)]

theorem spacedColor_add_period (k n : Nat) :
    spacedColor k (spacedPeriod k + n) = spacedColor k n := by
  simp only [spacedColor, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

theorem spacedColor_add_mod (k n j : Nat) :
    spacedColor k (n % spacedPeriod k + j) = spacedColor k (n + j) := by
  simp only [spacedColor, Nat.add_mod, Nat.mod_mod]

theorem collisionMarker_at_start (k : Nat) : HasCollisionMarker (spacedColor k) 107 := by
  intro j
  have hh := (collisionMarker_checks.1 ⟨107, by decide⟩).mpr rfl j
  change spacedColor 0 (107 + j.val) = _ at hh
  rw [spacedColor_common_collision 0 _ (by omega)] at hh
  rw [spacedColor_common_collision k _ (by omega)]
  exact hh

theorem spacedColor_last_window (k n : Nat) (_hk : 0 < k)
    (hlo : 548 <= n) (hhi : n < spacedPeriod k) (hlast : spacedPeriod k <= n + 5)
    (j : Fin 6) :
    spacedColor k (n + j.val) = spacedColor 1 (652 - (spacedPeriod k - n) + j.val) := by
  let m := 652 - (spacedPeriod k - n)
  have hm : 647 <= m ∧ m < 652 := by dsimp [m]; omega
  have he : n + 652 = spacedPeriod k + m := by dsimp [m]; omega
  change spacedColor k (n + j.val) = spacedColor 1 (m + j.val)
  by_cases hbefore : n + j.val < spacedPeriod k
  · rw [spacedColor_standard k _ (by omega) hbefore,
      spacedColor_standard 1 _ (by omega) (by change _ < 652; omega)]
    have hmod : (n + j.val - 548) % 104 = (m + j.val - 548) % 104 := by
      unfold spacedPeriod at he
      omega
    simp only [certifiedColor, hmod]
  · have hn : n + j.val = spacedPeriod k + (n + j.val - spacedPeriod k) := by omega
    have hm' : m + j.val = spacedPeriod 1 + (n + j.val - spacedPeriod k) := by
      change _ = 652 + _
      omega
    rw [hn, hm', spacedColor_add_period, spacedColor_add_period]
    rw [spacedColor_common_collision k _ (by omega), spacedColor_common_collision 1 _ (by omega)]

theorem collisionMarker_unique_in_period (k n : Nat) (hn : n < spacedPeriod k)
    (h : HasCollisionMarker (spacedColor k) n) : n = 107 := by
  by_cases hk : k = 0
  · subst k
    exact (collisionMarker_checks.1 ⟨n, hn⟩).mp h
  · have hkpos : 0 < k := by omega
    by_cases hhead : n < 548
    · apply (collisionMarker_checks.2.1 ⟨n, by omega⟩).mp
      change HasCollisionMarker (spacedColor 1) n
      intro j
      rw [← spacedColor_common_prefix k _ hkpos (by omega)]
      exact h j
    · by_cases hlast : spacedPeriod k <= n + 5
      · let m := 652 - (spacedPeriod k - n)
        have hm : 647 <= m ∧ m < 652 := by dsimp [m]; omega
        have hh : HasCollisionMarker (spacedColor 1) m := by
          intro j
          rw [← spacedColor_last_window k n hkpos (by omega) hn hlast j]
          exact h j
        have he := (collisionMarker_checks.2.1 ⟨m, hm.2⟩).mp hh
        change m = 107 at he
        omega
      · have hm : (n - 548) % 104 < 104 := Nat.mod_lt _ (by decide)
        apply False.elim (collisionMarker_checks.2.2 ⟨(n - 548) % 104, hm⟩ ?_)
        intro j
        have hh := h j
        rw [spacedColor_standard k _ (by omega) (by omega)] at hh
        have ht : n + j.val - 548 = (n - 548) + j.val := by omega
        rw [ht] at hh
        simpa only [certifiedColor, Nat.add_mod, Nat.mod_mod] using hh

theorem collisionMarker_iff (k n : Nat) :
    HasCollisionMarker (spacedColor k) n ↔ n % spacedPeriod k = 107 := by
  have hP : 0 < spacedPeriod k := by unfold spacedPeriod; omega
  constructor
  · intro h
    apply collisionMarker_unique_in_period k _ (Nat.mod_lt _ hP)
    intro j
    rw [spacedColor_add_mod]
    exact h j
  · intro h
    intro j
    rw [← spacedColor_add_mod, h]
    exact collisionMarker_at_start k j

end LangtonsAnt
