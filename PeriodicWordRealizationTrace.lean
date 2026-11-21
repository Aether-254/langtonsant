import PeriodicWord

namespace LangtonsAnt

/-- Repeat just the specified finite prefix; values outside it have no effect. -/
def repeatWord (P : Nat) (w : Nat -> Bool) : Nat -> Bool := fun n => w (n % P)

theorem repeatWord_prefix {P : Nat} (w : Nat -> Bool) {i : Nat} (hi : i < P) :
    repeatWord P w i = w i := by simp only [repeatWord, Nat.mod_eq_of_lt hi]

theorem repeatWord_trace {P : Nat} (w : Nat -> Bool) {n : Nat} (hn : n <= P) :
    wordTrace (repeatWord P w) n = wordTrace w n :=
  wordTrace_congr (fun i hi => repeatWord_prefix w (by omega))

theorem repeatWord_drift (P : Nat) (w : Nat -> Bool) :
    wordDrift P (repeatWord P w) = wordDrift P w :=
  congrArg Prod.fst (repeatWord_trace w (Nat.le_refl P))

theorem repeatWord_trace_period {P : Nat} {w : Nat -> Bool}
    (hd : (wordTrace w P).2 = .north) (n : Nat) :
    wordTrace (repeatWord P w) (n + P) =
      (addPoint (wordDrift P w) (wordPos (repeatWord P w) n),
        (wordTrace (repeatWord P w) n).2) := by
  induction n with
  | zero =>
    rw [Nat.zero_add, repeatWord_trace w (Nat.le_refl P)]
    exact Prod.ext (by simp [wordPos, wordTrace, wordDrift]) hd
  | succ n ih =>
    rw [show n + 1 + P = (n + P) + 1 by omega]
    simp only [wordTrace, ih, repeatWord, Nat.add_mod_right, wordPos, move_addPoint]

theorem repeatWord_pos_blocks {P : Nat} {w : Nat -> Bool}
    (hd : (wordTrace w P).2 = .north) (k j : Nat) :
    wordPos (repeatWord P w) (P * k + j) =
      addPoint (wordPos (repeatWord P w) j) (scalePoint (wordDrift P w) (k : Int)) := by
  induction k with
  | zero => simp [scalePoint]
  | succ k ih =>
    have he : P * (k + 1) + j = (P * k + j) + P := by rw [Nat.mul_succ]; omega
    have hp := congrArg Prod.fst (repeatWord_trace_period hd (P * k + j))
    change wordPos (repeatWord P w) (P * k + j + P) =
      addPoint (wordDrift P w) (wordPos (repeatWord P w) (P * k + j)) at hp
    rw [he, hp, ih]
    apply Prod.ext <;> simp [addPoint, scalePoint, Int.add_mul] <;> omega

theorem repeatWord_position {P : Nat} {w : Nat -> Bool}
    (hd : (wordTrace w P).2 = .north) (n : Nat) :
    wordPos (repeatWord P w) n = addPoint (wordPos (repeatWord P w) (n % P))
      (scalePoint (wordDrift P w) (n / P : Nat)) := by
  have h := repeatWord_pos_blocks hd (n / P) (n % P)
  simpa only [Nat.div_add_mod] using h

theorem repeatWord_phase_injective {P : Nat} {w : Nat -> Bool}
    (hd : (wordTrace w P).2 = .north) (hv : wordDrift P w ≠ (0, 0)) {n m : Nat}
    (hp : wordPos (repeatWord P w) n = wordPos (repeatWord P w) m)
    (hr : n % P = m % P) : n = m := by
  rw [repeatWord_position hd n, repeatWord_position hd m, hr] at hp
  have he : scalePoint (wordDrift P w) (n / P : Nat) = scalePoint (wordDrift P w) (m / P : Nat) := by
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    apply Prod.ext <;> simp only [addPoint] at hx hy ⊢ <;> omega
  have hq := scalePoint_injective hv he
  have hn := Nat.div_add_mod n P
  have hm := Nat.div_add_mod m P
  have : n / P = m / P := by omega
  rw [this] at hn
  omega

/-- Visits of the prescribed path, before it is known to obey the ant's board reads. -/
def wordEarlierVisits (u : Nat -> Bool) (n : Nat) (p : Point) : List Nat :=
  (List.range n).filter (fun j => decide (wordPos u j = p))

theorem mem_wordEarlierVisits (u : Nat -> Bool) (n : Nat) (p : Point) (j : Nat) :
    j ∈ wordEarlierVisits u n p ↔ j < n ∧ wordPos u j = p := by simp [wordEarlierVisits]

theorem repeatWord_visits_phase_iff {P : Nat} {w : Nat -> Bool}
    (hd : (wordTrace w P).2 = .north) (hv : wordDrift P w ≠ (0, 0))
    (hP : 0 < P) {K i : Nat} (hK : 2 * P <= K) (hi : i < P) (j : Nat) :
    (exists n, n < P * K + i ∧ wordPos (repeatWord P w) n =
      wordPos (repeatWord P w) (P * K + i) ∧ n % P = j) ↔
        j ∈ priorPhases P (repeatWord P w) i := by
  rw [mem_priorPhases (by rw [repeatWord_drift]; exact hv)]
  simp only [EarlierPhase, repeatWord_drift]
  constructor
  · rintro ⟨n, hn, he, rfl⟩
    refine ⟨Nat.mod_lt _ hP, ?_⟩
    have hq : n / P <= K := by
      have hh := Nat.div_le_div_right (Nat.le_of_lt hn) (c := P)
      simpa [Nat.mul_add_div hP, Nat.div_eq_of_lt hi] using hh
    have hdecomp := Nat.div_add_mod n P
    rw [repeatWord_position hd n, repeatWord_pos_blocks hd K i] at he
    by_cases hsame : n / P = K
    · left
      refine ⟨by rw [hsame] at hdecomp; omega, ?_⟩
      rw [hsame] at he
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      apply Prod.ext <;> simp only [addPoint] at hx hy ⊢ <;> omega
    · right
      refine ⟨K - n / P, by omega, ?_⟩
      have hcast : ((K - n / P : Nat) : Int) = (K : Int) - (n / P : Nat) := by omega
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      apply Prod.ext <;> simp only [addPoint, scalePoint, hcast, Int.sub_mul] at hx hy ⊢ <;> omega
  · rintro ⟨hj, (⟨hji, he⟩ | ⟨t, ht, he⟩)⟩
    · refine ⟨P * K + j, by omega, ?_, by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]⟩
      rw [repeatWord_pos_blocks hd K j, repeatWord_pos_blocks hd K i, he]
    · have hbound : t <= 2 * P := by
        apply period_overlap_bound (w := repeatWord P w) hi hj (by rw [repeatWord_drift]; exact hv)
        simpa only [repeatWord_drift] using he
      have hmul := Nat.mul_le_mul_left P (show K - t + 1 <= K by omega)
      rw [Nat.mul_succ] at hmul
      refine ⟨P * (K - t) + j, by omega, ?_, by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]⟩
      rw [repeatWord_pos_blocks hd (K - t) j, repeatWord_pos_blocks hd K i, he]
      have hcast : ((K - t : Nat) : Int) = (K : Int) - (t : Int) := by omega
      apply Prod.ext <;> simp only [addPoint, scalePoint, hcast, Int.sub_mul] <;> omega

theorem repeatWord_visits_phase_perm {P : Nat} {w : Nat -> Bool}
    (hd : (wordTrace w P).2 = .north) (hv : wordDrift P w ≠ (0, 0))
    (hP : 0 < P) {K i : Nat} (hK : 2 * P <= K) (hi : i < P) :
    ((wordEarlierVisits (repeatWord P w) (P * K + i)
      (wordPos (repeatWord P w) (P * K + i))).map (fun n => n % P)).Perm
        (priorPhases P w i) := by
  have hnodup : ((wordEarlierVisits (repeatWord P w) (P * K + i)
      (wordPos (repeatWord P w) (P * K + i))).map (fun n => n % P)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (List.nodup_range.filter _)
    intro n m hn hm hne heq
    have hp1 := ((mem_wordEarlierVisits _ _ _ n).mp hn).2
    have hp2 := ((mem_wordEarlierVisits _ _ _ m).mp hm).2
    exact hne (repeatWord_phase_injective hd hv (hp1.trans hp2.symm) heq)
  have hcongr : priorPhases P (repeatWord P w) i = priorPhases P w i :=
    priorPhases_congr (fun j hj => repeatWord_prefix w hj) hi
  rw [← hcongr]
  apply (List.perm_ext_iff_of_nodup hnodup (priorPhases_nodup _ _ _)).mpr
  intro j
  simp only [List.mem_map, mem_wordEarlierVisits]
  simpa only [and_assoc] using repeatWord_visits_phase_iff hd hv hP hK hi j

end LangtonsAnt
