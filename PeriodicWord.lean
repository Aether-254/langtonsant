import PeriodicWordCore

namespace LangtonsAnt

theorem wordTrace_reads {s : State} (hp : s.pos = (0, 0)) (hd : s.dir = .north) (n : Nat) :
    wordTrace (readColor s) n = ((run s n).pos, (run s n).dir) := by
  induction n with
  | zero => simp [wordTrace, hp, hd]
  | succ n ih => simp only [wordTrace, ih, readColor, run_succ, step]

theorem HighwayFrom.word_blocks {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (k j : Nat) :
    (run s (P * k + j)).pos = addPoint (run s j).pos (scalePoint v (k : Int)) ∧
    readColor s (P * k + j) = readColor s j := by
  induction k with
  | zero => simp [scalePoint]
  | succ k ih =>
    have he : P * (k + 1) + j = P * k + j + P := by rw [Nat.mul_succ]; omega
    rw [he, (h _ (by omega)).1, h.reads_periodic (by omega), ih.1, ih.2]
    constructor
    · apply Prod.ext <;> simp [addPoint, scalePoint, Int.add_mul, Int.add_assoc]
    · rfl

theorem HighwayFrom.word_position {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (n : Nat) :
    (run s n).pos = addPoint (run s (n % P)).pos (scalePoint v (n / P : Nat)) := by
  have hh := (h.word_blocks (n / P) (n % P)).1
  simpa only [Nat.div_add_mod] using hh

/-- Visits before time `n`; the current read is deliberately excluded. -/
def earlierVisits (s : State) (n : Nat) (p : Point) : List Nat :=
  (List.range n).filter (fun j => decide ((run s j).pos = p))

theorem mem_earlierVisits (s : State) (n : Nat) (p : Point) (j : Nat) :
    j ∈ earlierVisits s n p ↔ j < n ∧ (run s j).pos = p := by
  simp [earlierVisits]

theorem earlierVisits_nodup (s : State) (n : Nat) (p : Point) :
    (earlierVisits s n p).Nodup := List.nodup_range.filter _

theorem board_visit_parity (s : State) (p : Point) (n : Nat) :
    (run s n).board p = (s.board p ^^ decide ((earlierVisits s n p).length % 2 = 1)) := by
  induction n with
  | zero => simp [earlierVisits]
  | succ n ih =>
    have he : (earlierVisits s (n + 1) p).length =
        (earlierVisits s n p).length + if (run s n).pos = p then 1 else 0 := by
      simp [earlierVisits, List.range_succ, List.filter_append]
      split <;> simp_all
    rw [he, run_succ]
    change flip (run s n).board (run s n).pos p = _
    by_cases hp : (run s n).pos = p
    · rw [ite_eq_left hp, hp, flip_same, ih]
      by_cases hc : (earlierVisits s n p).length % 2 = 1
      · simp [hc, show ((earlierVisits s n p).length + 1) % 2 = 0 by omega]
      · simp [hc, show ((earlierVisits s n p).length + 1) % 2 = 1 by omega]
    · simp [flip, Ne.symm hp, ih, hp]

theorem HighwayFrom.phase_injective {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (hv : v ≠ (0, 0)) {n m : Nat}
    (hp : (run s n).pos = (run s m).pos) (hr : n % P = m % P) : n = m := by
  rw [h.word_position n, h.word_position m, hr] at hp
  have he : scalePoint v (n / P : Nat) = scalePoint v (m / P : Nat) := by
    apply Prod.ext
    · have hx := congrArg Prod.fst hp
      simp only [addPoint] at hx
      omega
    · have hy := congrArg Prod.snd hp
      simp only [addPoint] at hy
      omega
  have hq := scalePoint_injective hv he
  have hn := Nat.div_add_mod n P
  have hm := Nat.div_add_mod m P
  have : n / P = m / P := by omega
  rw [this] at hn
  omega

/-- At each phase, arbitrarily late copies are initially white. -/
theorem HighwayFrom.exists_white_copy {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (hs : FiniteSupport s.board) (hP : 0 < P)
    (i B : Nat) : exists K, B <= K ∧ s.board (run s (P * K + i)).pos = false := by
  classical
  obtain ⟨cells, hc⟩ := hs
  have hv := h.drift_ne_zero hP
  apply Classical.byContradiction
  intro hn
  have hall (k : Nat) : (run s (P * (B + k) + i)).pos ∈ cells := by
    apply hc
    have hb : s.board (run s (P * (B + k) + i)).pos ≠ false := by
      intro hh
      exact hn ⟨B + k, by omega, hh⟩
    cases he : s.board (run s (P * (B + k) + i)).pos <;> simp_all
  obtain ⟨n, m, hnm, he⟩ := finite_list_repeats cells
    (fun k => (run s (P * (B + k) + i)).pos) hall
  have ht := h.phase_injective hv he (by simp [Nat.add_mod])
  have hcancel : B + n = B + m := Nat.eq_of_mul_eq_mul_left hP (by omega)
  omega

theorem wordPos_reads {s : State} (hp : s.pos = (0, 0)) (hd : s.dir = .north) (n : Nat) :
    wordPos (readColor s) n = (run s n).pos := congrArg Prod.fst (wordTrace_reads hp hd n)

theorem HighwayFrom.word_drift {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (hp : s.pos = (0, 0)) (hd : s.dir = .north) :
    wordDrift P (readColor s) = v := by
  have he := (h 0 (by omega)).1
  simpa [wordDrift, wordPos_reads hp hd, hp] using he

/-- The phase map is a bijection from actual earlier visits to the infinite past phases. -/
theorem HighwayFrom.visits_phase_iff {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hP : 0 < P) {K i : Nat} (hK : 2 * P <= K) (hi : i < P) (j : Nat) :
    (exists n, n < P * K + i ∧ (run s n).pos = (run s (P * K + i)).pos ∧ n % P = j) ↔
      j ∈ priorPhases P (readColor s) i := by
  have hv := h.drift_ne_zero hP
  have hdv := h.word_drift hp hd
  rw [mem_priorPhases (by rw [hdv]; exact hv)]
  simp only [EarlierPhase, hdv, wordPos_reads hp hd]
  constructor
  · rintro ⟨n, hn, he, rfl⟩
    refine ⟨Nat.mod_lt _ hP, ?_⟩
    have hq : n / P <= K := by
      have hh := Nat.div_le_div_right (Nat.le_of_lt hn) (c := P)
      simpa [Nat.mul_add_div hP, Nat.div_eq_of_lt hi] using hh
    have hdecomp := Nat.div_add_mod n P
    rw [h.word_position n, (h.word_blocks K i).1] at he
    by_cases hsame : n / P = K
    · left
      refine ⟨by rw [hsame] at hdecomp; omega, ?_⟩
      rw [hsame] at he
      apply Prod.ext
      · have hh := congrArg Prod.fst he
        simp only [addPoint] at hh
        omega
      · have hh := congrArg Prod.snd he
        simp only [addPoint] at hh
        omega
    · right
      refine ⟨K - n / P, by omega, ?_⟩
      have hcast : ((K - n / P : Nat) : Int) = (K : Int) - (n / P : Nat) := by omega
      apply Prod.ext
      · have hh := congrArg Prod.fst he
        simp only [addPoint, scalePoint, hcast, Int.sub_mul] at hh ⊢
        omega
      · have hh := congrArg Prod.snd he
        simp only [addPoint, scalePoint, hcast, Int.sub_mul] at hh ⊢
        omega
  · rintro ⟨hj, (⟨hji, he⟩ | ⟨t, ht, he⟩)⟩
    · refine ⟨P * K + j, by omega, ?_, by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]⟩
      rw [(h.word_blocks K j).1, (h.word_blocks K i).1, he]
    · have hbound : t <= 2 * P := by
        apply period_overlap_bound (w := readColor s) hi hj (by rw [hdv]; exact hv)
        simpa only [wordPos_reads hp hd, hdv] using he
      have htk : t <= K := by omega
      have hmul := Nat.mul_le_mul_left P (show K - t + 1 <= K by omega)
      rw [Nat.mul_succ] at hmul
      refine ⟨P * (K - t) + j, by omega, ?_, by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]⟩
      rw [(h.word_blocks (K - t) j).1, (h.word_blocks K i).1, he]
      have hcast : ((K - t : Nat) : Int) = (K : Int) - (t : Int) := by omega
      apply Prod.ext <;> simp only [addPoint, scalePoint, hcast, Int.sub_mul] <;> omega

theorem HighwayFrom.visits_phase_perm {s : State} {P : Nat} {v : Point}
    (h : HighwayFrom s 0 P v) (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hP : 0 < P) {K i : Nat} (hK : 2 * P <= K) (hi : i < P) :
    ((earlierVisits s (P * K + i) (run s (P * K + i)).pos).map (fun n => n % P)).Perm
      (priorPhases P (readColor s) i) := by
  have hnodup : ((earlierVisits s (P * K + i) (run s (P * K + i)).pos).map
      (fun n => n % P)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (earlierVisits_nodup s _ _)
    intro n m hn hm hne heq
    have hp1 := ((mem_earlierVisits s _ _ n).mp hn).2
    have hp2 := ((mem_earlierVisits s _ _ m).mp hm).2
    exact hne (h.phase_injective (h.drift_ne_zero hP) (hp1.trans hp2.symm) heq)
  apply (List.perm_ext_iff_of_nodup hnodup (priorPhases_nodup _ _ _)).mpr
  intro j
  simp only [List.mem_map, mem_earlierVisits]
  simpa only [and_assoc] using h.visits_phase_iff hp hd hP hK hi j

theorem periodic_word_consistent_at_origin {s : State} {P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hP : 0 < P) (h : HighwayFrom s 0 P v) : ConsistentWord P (readColor s) := by
  refine ⟨?_, ?_, ?_⟩
  · have he := (h 0 (by omega)).2
    simpa [wordTrace_reads hp hd, hd] using he
  · rw [h.word_drift hp hd]
    exact h.drift_ne_zero hP
  · intro i hi
    obtain ⟨K, hK, hw⟩ := h.exists_white_copy hs hP i (2 * P)
    have hc := board_visit_parity s (run s (P * K + i)).pos (P * K + i)
    rw [hw, Bool.false_xor] at hc
    have hlen := (h.visits_phase_perm hp hd hP hK hi).length_eq
    simp only [List.length_map] at hlen
    rw [hlen] at hc
    exact (h.word_blocks K i).2.symm.trans hc

/-- Every finite-support periodic tail already has a white-background consistent turn word.
Rotation changes coordinates, but preserves the turn word and all visit multiplicities. -/
theorem periodic_tail_consistent_at_start {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    ConsistentWord P (fun i => readColor s (T + i)) := by
  let t := run s T
  let u := normalize t.dir t.pos t
  have ht : HighwayFrom t 0 P v := by
    intro n _
    have hh := h (T + n) (by omega)
    simpa only [t, ← run_add, Nat.add_assoc] using hh
  have hu : HighwayFrom u 0 P (rotatePoint (inverseRotation t.dir) v) :=
    (ht.translate (negPoint t.pos)).rotate (inverseRotation t.dir)
  have hup : u.pos = (0, 0) := by
    have hz : addPoint (negPoint t.pos) t.pos = (0, 0) := by
      apply Prod.ext <;> simp only [addPoint, negPoint] <;> omega
    change rotatePoint (inverseRotation t.dir) (addPoint (negPoint t.pos) t.pos) = _
    rw [hz, rotatePoint_zero]
  have hud : u.dir = .north := by
    change rotateDir (inverseRotation t.dir) t.dir = .north
    have he := rotateDir_inverse t.dir .north
    simpa only [rotateDir_north] using he
  have hc := periodic_word_consistent_at_origin
    (finiteSupport_normalize (finiteSupport_run s hs T) t.dir t.pos) hup hud hP hu
  have hr : readColor u = fun i => readColor s (T + i) := by
    funext i
    rw [show readColor u i = readColor t i from normalize_readColor t.dir t.pos t i]
    simp only [t, readColor, run_add]
  rw [hr] at hc
  exact hc

theorem periodic_tail_consistent {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (h : HighwayFrom s T P v) :
    exists U, T <= U ∧ ConsistentWord P (fun i => readColor s (U + i)) :=
  ⟨T, Nat.le_refl T, periodic_tail_consistent_at_start hs hP h⟩

theorem no_odd_periodic_tail {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (hodd : P % 2 = 1) :
    ¬ HighwayFrom s T P v := by
  intro h
  exact no_consistent_word_odd hodd _ (periodic_tail_consistent_at_start hs hP h)

theorem standard_word_consistent : ConsistentWord 104 certifiedColor := by
  have hh := periodic_tail_consistent_at_start highwaySeed_finite (by decide) highwaySeed_highway
  simpa only [Nat.zero_add, highwaySeed_exact_reads] using hh

end LangtonsAnt
