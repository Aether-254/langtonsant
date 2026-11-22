import PeriodicWordRealization

namespace LangtonsAnt

/-- A background invariant under the full drift; the first read need not be white. -/
def BackgroundWord (P : Nat) (w : Nat -> Bool) (background : Board) : Prop :=
  (wordTrace w P).2 = .north ∧ wordDrift P w ≠ (0, 0) ∧
    (forall p, background (addPoint p (wordDrift P w)) = background p) ∧
    forall i, i < P -> w i = Bool.xor (background (wordPos w i))
      (decide ((priorPhases P w i).length % 2 = 1))

def backgroundState (background : Board) (u : Nat -> Bool) (n : Nat) : State :=
  { board := fun p => Bool.xor (prescribedBoard u n p) (background p)
    pos := wordPos u n, dir := (wordTrace u n).2 }

theorem background_scaled {v : Point} {background : Board}
    (h : forall p, background (addPoint p v) = background p) (p : Point) (k : Nat) :
    background (addPoint p (scalePoint v (k : Int))) = background p := by
  induction k with
  | zero => simp [scalePoint]
  | succ k ih =>
    have he : addPoint p (scalePoint v ((k + 1 : Nat) : Int)) =
        addPoint (addPoint p (scalePoint v (k : Int))) v := by
      apply Prod.ext <;> simp [addPoint, scalePoint, Int.add_mul] <;> omega
    rw [he, h, ih]

theorem BackgroundWord.prescribed_read {P : Nat} {w : Nat -> Bool} {background : Board}
    (h : BackgroundWord P w background) (hP : 0 < P) (n : Nat) (hn : P * (2 * P) <= n) :
    (backgroundState background (repeatWord P w) n).board
      (wordPos (repeatWord P w) n) = repeatWord P w n := by
  have hK : 2 * P <= n / P := by
    have hh := Nat.div_le_div_right hn (c := P)
    simpa only [Nat.mul_div_right _ hP] using hh
  have hi := Nat.mod_lt n hP
  have hp := repeatWord_visits_phase_perm h.1 h.2.1 hP hK hi
  rw [Nat.div_add_mod] at hp
  have hlen := hp.length_eq
  simp only [List.length_map] at hlen
  have hb : background (wordPos (repeatWord P w) n) = background (wordPos w (n % P)) := by
    rw [repeatWord_position h.1, background_scaled h.2.2.1]
    exact congrArg background (congrArg Prod.fst (repeatWord_trace w (Nat.le_of_lt hi)))
  change Bool.xor (prescribedBoard (repeatWord P w) n (wordPos (repeatWord P w) n))
    (background (wordPos (repeatWord P w) n)) = _
  rw [prescribedBoard_parity, hlen, hb, Bool.xor_comm]
  exact (h.2.2.2 _ hi).symm

theorem backgroundState_step {background : Board} {u : Nat -> Bool} {n : Nat}
    (h : (backgroundState background u n).board (wordPos u n) = u n) :
    step (backgroundState background u n) = backgroundState background u (n + 1) := by
  have hf : flip (fun p => Bool.xor (prescribedBoard u n p) (background p)) (wordPos u n) =
      fun p => Bool.xor (flip (prescribedBoard u n) (wordPos u n) p) (background p) := by
    funext p
    by_cases he : p = wordPos u n
    · subst p
      simp only [flip_same]
      cases prescribedBoard u n (wordPos u n) <;> cases background (wordPos u n) <;> rfl
    · simp [flip, he]
  simp only [backgroundState] at h
  simp only [wordPos] at h hf
  simp only [step, backgroundState, prescribedBoard, wordPos, wordTrace]
  rw [h, hf]

def backgroundRealization (P : Nat) (w : Nat -> Bool) (background : Board) : State :=
  backgroundState background (repeatWord P w) (P * (2 * P))

theorem BackgroundWord.realization_run {P : Nat} {w : Nat -> Bool} {background : Board}
    (h : BackgroundWord P w background) (hP : 0 < P) (n : Nat) :
    run (backgroundRealization P w background) n =
      backgroundState background (repeatWord P w) (P * (2 * P) + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih]
    exact backgroundState_step (h.prescribed_read hP _ (by omega))

theorem BackgroundWord.realization_reads {P : Nat} {w : Nat -> Bool} {background : Board}
    (h : BackgroundWord P w background) (hP : 0 < P) (n : Nat) :
    readColor (backgroundRealization P w background) n = w (n % P) := by
  unfold readColor
  rw [h.realization_run hP]
  rw [show (backgroundState background (repeatWord P w) (P * (2 * P) + n)).pos =
    wordPos (repeatWord P w) (P * (2 * P) + n) from rfl]
  rw [h.prescribed_read hP _ (by omega)]
  simp only [repeatWord, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]

theorem BackgroundWord.realization_highway {P : Nat} {w : Nat -> Bool} {background : Board}
    (h : BackgroundWord P w background) (hP : 0 < P) :
    HighwayFrom (backgroundRealization P w background) 0 P (wordDrift P w) := by
  intro n _
  rw [h.realization_run hP, h.realization_run hP]
  have ht := repeatWord_trace_period h.1 (P * (2 * P) + n)
  have hp := congrArg Prod.fst ht
  have hd := congrArg Prod.snd ht
  constructor
  · simpa only [backgroundState, wordPos, Nat.add_assoc, addPoint, Int.add_comm] using hp
  · simpa only [backgroundState, Nat.add_assoc] using hd

end LangtonsAnt
