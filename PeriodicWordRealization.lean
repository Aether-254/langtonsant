import PeriodicWordRealizationTrace

namespace LangtonsAnt

/-- Flip the cells on a prescribed path; the turns need not yet agree with the board. -/
def prescribedBoard (u : Nat -> Bool) : Nat -> Board
  | 0 => fun _ => false
  | n + 1 => flip (prescribedBoard u n) (wordPos u n)

def prescribedState (u : Nat -> Bool) (n : Nat) : State :=
  { board := prescribedBoard u n, pos := wordPos u n, dir := (wordTrace u n).2 }

theorem prescribedBoard_support (u : Nat -> Bool) (n : Nat) :
    forall p, prescribedBoard u n p = true -> p ∈ (List.range n).map (wordPos u) := by
  induction n with
  | zero => intro p hp; contradiction
  | succ n ih =>
    intro p hp
    rw [List.range_succ, List.map_append, List.mem_append]
    by_cases he : p = wordPos u n
    · exact Or.inr (by simp [he])
    · left
      apply ih p
      simpa only [prescribedBoard, flip_other _ he] using hp

theorem prescribedBoard_finite (u : Nat -> Bool) (n : Nat) : FiniteSupport (prescribedBoard u n) :=
  ⟨(List.range n).map (wordPos u), prescribedBoard_support u n⟩

theorem prescribedBoard_parity (u : Nat -> Bool) (n : Nat) (p : Point) :
    prescribedBoard u n p = decide ((wordEarlierVisits u n p).length % 2 = 1) := by
  induction n with
  | zero => simp [prescribedBoard, wordEarlierVisits]
  | succ n ih =>
    have he : (wordEarlierVisits u (n + 1) p).length =
        (wordEarlierVisits u n p).length + if wordPos u n = p then 1 else 0 := by
      simp [wordEarlierVisits, List.range_succ, List.filter_append]
      split <;> simp_all
    rw [he]
    change flip (prescribedBoard u n) (wordPos u n) p = _
    by_cases hp : wordPos u n = p
    · rw [ite_eq_left hp, hp, flip_same, ih]
      by_cases hc : (wordEarlierVisits u n p).length % 2 = 1
      · simp [hc, show ((wordEarlierVisits u n p).length + 1) % 2 = 0 by omega]
      · simp [hc, show ((wordEarlierVisits u n p).length + 1) % 2 = 1 by omega]
    · simp [flip, Ne.symm hp, ih, hp]

/-- After finitely many prescribed cycles, every board read obeys the given word. -/
theorem ConsistentWord.prescribed_read {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (n : Nat) (hn : P * (2 * P) <= n) :
    prescribedBoard (repeatWord P w) n (wordPos (repeatWord P w) n) = repeatWord P w n := by
  have hK : 2 * P <= n / P := by
    have hh := Nat.div_le_div_right hn (c := P)
    simpa only [Nat.mul_div_right _ hP] using hh
  have hi := Nat.mod_lt n hP
  have hp := repeatWord_visits_phase_perm h.1 h.2.1 hP hK hi
  have he : P * (n / P) + n % P = n := Nat.div_add_mod n P
  rw [he] at hp
  have hlen := hp.length_eq
  simp only [List.length_map] at hlen
  rw [prescribedBoard_parity, hlen]
  exact (h.2.2 (n % P) hi).symm

theorem prescribedState_step {u : Nat -> Bool} {n : Nat}
    (h : prescribedBoard u n (wordPos u n) = u n) :
    step (prescribedState u n) = prescribedState u (n + 1) := by
  simp only [step, prescribedState, prescribedBoard, wordPos, wordTrace] at h ⊢
  rw [h]

/-- A finite board obtained from the first `2*P` prescribed cycles. -/
def wordRealization (P : Nat) (w : Nat -> Bool) : State :=
  prescribedState (repeatWord P w) (P * (2 * P))

theorem wordRealization_finite (P : Nat) (w : Nat -> Bool) :
    FiniteSupport (wordRealization P w).board := prescribedBoard_finite _ _

theorem wordRealization_support_bound (P : Nat) (w : Nat -> Bool) :
    exists cells : List Point, cells.length = 2 * P * P ∧
      forall p, (wordRealization P w).board p = true -> p ∈ cells := by
  refine ⟨(List.range (P * (2 * P))).map (wordPos (repeatWord P w)), ?_, prescribedBoard_support _ _⟩
  simp only [List.length_map, List.length_range]
  exact Nat.mul_comm P (2 * P)

theorem ConsistentWord.realization_run {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (n : Nat) :
    run (wordRealization P w) n = prescribedState (repeatWord P w) (P * (2 * P) + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih]
    exact prescribedState_step (h.prescribed_read hP _ (by omega))

theorem ConsistentWord.realization_reads {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (n : Nat) :
    readColor (wordRealization P w) n = w (n % P) := by
  unfold readColor
  rw [h.realization_run hP]
  change prescribedBoard (repeatWord P w) (P * (2 * P) + n)
    (wordPos (repeatWord P w) (P * (2 * P) + n)) = _
  rw [h.prescribed_read hP _ (by omega)]
  simp only [repeatWord, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]

theorem ConsistentWord.realization_highway {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) :
    HighwayFrom (wordRealization P w) 0 P (wordDrift P w) := by
  intro n _
  rw [h.realization_run hP, h.realization_run hP]
  have ht := repeatWord_trace_period h.1 (P * (2 * P) + n)
  have hp := congrArg Prod.fst ht
  have hd := congrArg Prod.snd ht
  constructor
  · simpa only [prescribedState, wordPos, Nat.add_assoc, addPoint, Int.add_comm] using hp
  · simpa only [prescribedState, Nat.add_assoc] using hd

/-- Every positive-length consistent word is the exact read word of a finite-support highway. -/
theorem ConsistentWord.realizable {P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) :
    exists s : State, FiniteSupport s.board ∧ HighwayFrom s 0 P (wordDrift P w) ∧
      forall n, readColor s n = w (n % P) :=
  ⟨wordRealization P w, wordRealization_finite P w, h.realization_highway hP, h.realization_reads hP⟩

theorem consistentWord_iff_finite_realization {P : Nat} {w : Nat -> Bool} (hP : 0 < P) :
    ConsistentWord P w ↔
      exists s : State, FiniteSupport s.board ∧ HighwayFrom s 0 P (wordDrift P w) ∧
        forall n, readColor s n = w (n % P) := by
  constructor
  · exact fun h => h.realizable hP
  · rintro ⟨s, hs, hh, hr⟩
    have hc := periodic_tail_consistent_at_start hs hP hh
    apply hc.congr
    intro j hj
    simp only [Nat.zero_add, hr j, Nat.mod_eq_of_lt hj]

end LangtonsAnt
