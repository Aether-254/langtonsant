import HardPhaseRecovery

/-!
# Single black cells hit late by the blank highway

The blank ant enters the standard highway at time 12080 (`blank_entryAt`).  If a single
initial black cell `q` is first reached by the blank trajectory late enough, at a time whose
phase after the entry is not 49, then the perturbed state is eventually standard.

The proof is uniform in `q`: the first contact is a first visit of the seed highway, so its
phase is one of the 22 first-visit phases (`seed_firstVisit_iff`); for the 21 phases other
than 49 the history-independent recovery theorem applies to the blank history.

Phase 49 is excluded here: its recovery builds a northeast highway that crosses `x+y > 0`,
where the blank transient remnants lie, so `phase_forty_nine_recovers` does not apply directly.
Cells hit before the threshold form a finite set and are not treated here either.
-/

namespace LangtonsAnt

/-- From per-phase thresholds on a finite list, extract one common threshold. -/
theorem list_common_bound (l : List Nat) (P : Nat -> Nat -> Prop)
    (h : forall phi, phi ∈ l -> exists H, forall k, P phi (k + H)) :
    exists B, forall phi, phi ∈ l -> forall m, B <= m -> P phi m := by
  induction l with
  | nil => exact ⟨0, fun phi hphi => by simp at hphi⟩
  | cons a l ih =>
    obtain ⟨Ha, hHa⟩ := h a (by simp)
    obtain ⟨B, hB⟩ := ih (fun phi hphi => h phi (by simp [hphi]))
    refine ⟨max Ha B, fun phi hphi m hm => ?_⟩
    simp only [List.mem_cons] at hphi
    rcases hphi with rfl | hphi
    · have e : m = (m - Ha) + Ha := by omega
      rw [e]
      exact hHa (m - Ha)
    · exact hB phi hphi m (by omega)

/-- One threshold for all 21 history-independent first-visit phases. -/
theorem fresh_phase_common_bound :
    exists B, forall phi, phi ∈ freshPhases -> phi ≠ 49 -> forall m, B <= m ->
      forall s : State, AgreesBelow 0 s highwaySeed.toState ->
        EventuallyStandard (flipCell (run s (104 * m + phi)) (run s (104 * m + phi)).pos) := by
  obtain ⟨B, hB⟩ := list_common_bound freshPhases
    (fun phi m => phi ≠ 49 -> forall s : State, AgreesBelow 0 s highwaySeed.toState ->
      EventuallyStandard (flipCell (run s (104 * m + phi)) (run s (104 * m + phi)).pos))
    (by
      intro phi hphi
      by_cases h49 : phi = 49
      · exact ⟨0, fun _ hne => absurd h49 hne⟩
      · obtain ⟨H, hH⟩ := fresh_phase_recovers_except_49 phi hphi h49
        exact ⟨H, fun k _ s hs => hH s hs k⟩)
  exact ⟨B, fun phi hphi h49 m hm s hs => hB phi hphi m hm h49 s hs⟩


/-- Explicit form: every first-visit phase except 49 recovers once at least 18 periods of
history have passed (18 is the largest history length among the certificates, phase 6). -/
theorem fresh_phase_recovers_late {phi : Nat} (hphi : phi ∈ freshPhases) (h49 : phi ≠ 49)
    {m : Nat} (hm : 18 <= m) {s : State} (hs : AgreesBelow 0 s highwaySeed.toState) :
    EventuallyStandard (flipCell (run s (104 * m + phi)) (run s (104 * m + phi)).pos) := by
  simp only [freshPhases, List.mem_cons, List.not_mem_nil, or_false] at hphi
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨440, (-2, -2), diagonal_rotated_southwest .north,
      highway_flip_recovers_at_phase_four hs m⟩
  · -- phase 5, history 12
    have e : m = (m - 12) + 12 := by omega
    rw [e]
    exact mature_phase_five_certificate.eventually_shift (by decide) hs (m - 12)
  · -- phase 6, history 18
    have e : m = (m - 18) + 18 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_six_check).eventually_shift rfl hs (m - 18)
  · -- phase 9, history 7
    have e : m = (m - 7) + 7 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_nine_check).eventually_shift rfl hs (m - 7)
  · -- phase 15, history 8
    have e : m = (m - 8) + 8 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_fifteen_check).eventually_shift rfl hs (m - 8)
  · -- phase 22, history 8
    have e : m = (m - 8) + 8 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_twenty_two_check).eventually_shift rfl hs (m - 8)
  · -- phase 23, history 3
    have e : m = (m - 3) + 3 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_twenty_three_check).eventually_shift rfl hs (m - 3)
  · -- phase 24, history 3
    have e : m = (m - 3) + 3 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_twenty_four_check).eventually_shift rfl hs (m - 3)
  · -- phase 32, history 13
    have e : m = (m - 13) + 13 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_thirty_two_check).eventually_shift rfl hs (m - 13)
  · -- phase 33, history 8
    have e : m = (m - 8) + 8 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_thirty_three_check).eventually_shift rfl hs (m - 8)
  · -- phase 34, history 1
    have e : m = (m - 1) + 1 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_thirty_four_check).eventually_shift rfl hs (m - 1)
  · -- phase 37, history 10
    have e : m = (m - 10) + 10 := by omega
    rw [e]
    exact phase_thirty_seven_certificate.eventually_shift rfl hs (m - 10)
  · -- phase 38, history 13
    have e : m = (m - 13) + 13 := by omega
    rw [e]
    exact phase_thirty_eight_certificate.eventually_shift rfl hs (m - 13)
  · -- phase 39, history 13
    have e : m = (m - 13) + 13 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_thirty_nine_check).eventually_shift rfl hs (m - 13)
  · -- phase 47, history 3
    have e : m = (m - 3) + 3 := by omega
    rw [e]
    exact phase_forty_seven_certificate.eventually_shift rfl hs (m - 3)
  · -- phase 48, history 9
    have e : m = (m - 9) + 9 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_forty_eight_check).eventually_shift rfl hs (m - 9)
  · exact absurd rfl h49
  · -- phase 52, history 5
    have e : m = (m - 5) + 5 := by omega
    rw [e]
    exact phase_fifty_two_certificate.eventually_shift rfl hs (m - 5)
  · -- phase 66, history 0
    have e : m = (m - 0) + 0 := by omega
    rw [e]
    exact phase_sixty_six_certificate.eventually_shift (by decide) hs (m - 0)
  · -- phase 94, history 0
    have e : m = (m - 0) + 0 := by omega
    rw [e]
    exact phase_ninety_four_certificate.eventually_shift (by decide) hs (m - 0)
  · -- phase 95, history 0
    have e : m = (m - 0) + 0 := by omega
    rw [e]
    exact phase_ninety_five_certificate.eventually_shift (by decide) hs (m - 0)
  · -- phase 96, history 6
    have e : m = (m - 6) + 6 := by omega
    rw [e]
    exact (checkRotatedRecovery_sound phase_ninety_six_check).eventually_shift rfl hs (m - 6)

/-- The normalized blank state at its certified entry. -/
abbrev blankEntryState : State := normalize .north (-56, -30) (run blank 12080)

theorem blank_run_entry (n : Nat) :
    run blank (12080 + n) = pose .north (-56, -30) (run blankEntryState n) := by
  rw [run_add, ← pose_run, pose_normalize]

/-- A first contact of the blank orbit after its entry is a first visit of the seed orbit. -/
theorem blank_late_contact_firstVisit {q : Point} {n : Nat}
    (h : FirstContact (fun x => decide (x = q)) blank (12080 + n)) :
    FirstVisitAt highwaySeed.toState n := by
  have hq : (run blank (12080 + n)).pos = q := by simpa using h.1
  intro j hj he
  have hne := h.2 (12080 + j) (by omega)
  have hpos : (run blank (12080 + j)).pos = q := by
    rw [blank_tail_pos, he, ← blank_tail_pos, hq]
  simp [hpos] at hne

/-- Every single black cell first reached by the blank orbit late enough, at a phase other
than 49 after the entry, gives an eventually standard initial state. -/
theorem singleBlack_late_standard :
    exists T0 : Nat, forall (q : Point) (tau : Nat),
      FirstContact (fun x => decide (x = q)) blank tau -> T0 <= tau ->
      (tau - 12080) % 104 ≠ 49 -> EventuallyStandard (singleBlack q) := by
  obtain ⟨B, hB⟩ := fresh_phase_common_bound
  refine ⟨12080 + 104 * (max B 2), fun q tau hc hlate h49 => ?_⟩
  obtain ⟨n, rfl⟩ : exists n, tau = 12080 + n := ⟨tau - 12080, by omega⟩
  have hn : 12080 + n - 12080 = n := by omega
  rw [hn] at h49
  obtain ⟨m, phi, hphi, rfl⟩ : exists m phi, phi < 104 ∧ n = 104 * m + phi :=
    ⟨n / 104, n % 104, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 104).symm⟩
  have hm : max B 2 <= m := by omega
  have hmod : (104 * m + phi) % 104 = phi := by omega
  rw [hmod] at h49
  -- the contact phase is a first-visit phase
  have hfresh : phi ∈ freshPhases :=
    (seed_firstVisit_iff (by omega) hphi).mp (blank_late_contact_firstVisit hc)
  -- recovery in the normalized frame
  have hrec := hB phi hfresh h49 m (by omega) blankEntryState blank_entryAt
  have hpose := hrec.pose .north (-56, -30)
  rw [← flipCell_pose, ← blank_run_entry] at hpose
  -- the perturbed run equals the flipped blank run at the contact time
  have hq : (run blank (12080 + (104 * m + phi))).pos = q := by simpa using hc.1
  have he : run (singleBlack q) (12080 + (104 * m + phi)) =
      flipCell (run blank (12080 + (104 * m + phi)))
        (run blank (12080 + (104 * m + phi))).pos := by
    rw [singleBlack_eq_perturb, firstContact_state hc, flipCell_eq_perturb, hq]
  rw [← he] at hpose
  exact hpose.of_run

/-- Explicit threshold: first contact at time at least `13952 = 12080 + 104*18`, at a phase
other than 49 after the blank entry. -/
theorem singleBlack_late_explicit {q : Point} {tau : Nat}
    (hc : FirstContact (fun x => decide (x = q)) blank tau) (hlate : 13952 <= tau)
    (h49 : (tau - 12080) % 104 ≠ 49) : EventuallyStandard (singleBlack q) := by
  obtain ⟨n, rfl⟩ : exists n, tau = 12080 + n := ⟨tau - 12080, by omega⟩
  have hn : 12080 + n - 12080 = n := by omega
  rw [hn] at h49
  obtain ⟨m, phi, hphi, rfl⟩ : exists m phi, phi < 104 ∧ n = 104 * m + phi :=
    ⟨n / 104, n % 104, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 104).symm⟩
  have hm : 18 <= m := by omega
  have hmod : (104 * m + phi) % 104 = phi := by omega
  rw [hmod] at h49
  have hfresh : phi ∈ freshPhases :=
    (seed_firstVisit_iff (by omega) hphi).mp (blank_late_contact_firstVisit hc)
  have hrec := fresh_phase_recovers_late hfresh h49 hm blank_entryAt
  have hpose := hrec.pose .north (-56, -30)
  rw [← flipCell_pose, ← blank_run_entry] at hpose
  have hq : (run blank (12080 + (104 * m + phi))).pos = q := by simpa using hc.1
  have he : run (singleBlack q) (12080 + (104 * m + phi)) =
      flipCell (run blank (12080 + (104 * m + phi)))
        (run blank (12080 + (104 * m + phi))).pos := by
    rw [singleBlack_eq_perturb, firstContact_state hc, flipCell_eq_perturb, hq]
  rw [← he] at hpose
  exact hpose.of_run

end LangtonsAnt
