import VariableObstacleBlock

namespace LangtonsAnt

def scheduleTail (f : Nat -> Nat) (n : Nat) : Nat -> Nat := fun j => f (n + j)

def scheduleDistance (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => scheduleDistance f n + 4 + f n

def scheduleTime (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => scheduleTime f n + spacedPeriod (f n)

def scheduleOffset (f : Nat -> Nat) (n : Nat) : Point :=
  (-2 * (scheduleDistance f n : Int), -2 * (scheduleDistance f n : Int))

def schedulePoint (f : Nat -> Nat) (n : Nat) : Point := addPoint (scheduleOffset f n) chainHead

noncomputable def scheduleMask (f : Nat -> Nat) : Board := by
  classical
  exact fun p => decide (exists n : Nat, p = schedulePoint f n)

theorem scheduleMask_iff (f : Nat -> Nat) (p : Point) :
    scheduleMask f p = true ↔ exists n : Nat, p = schedulePoint f n := by
  classical
  simp only [scheduleMask, decide_eq_true_eq]

theorem scheduleMask_ahead (f : Nat -> Nat) : AheadMask (scheduleMask f) := by
  intro p hp
  obtain ⟨n, rfl⟩ := (scheduleMask_iff f p).mp hp
  refine ⟨scheduleDistance f n, ?_⟩
  apply Prod.ext <;> simp [schedulePoint, scheduleOffset, addPoint, chainHead] <;> omega

theorem scheduleDistance_tail (f : Nat -> Nat) (n : Nat) :
    scheduleDistance f (n + 1) = 4 + f 0 + scheduleDistance (scheduleTail f 1) n := by
  induction n with
  | zero => simp [scheduleDistance]
  | succ n ih =>
    change scheduleDistance f (n + 1) + 4 + f (n + 1) =
      4 + f 0 + (scheduleDistance (scheduleTail f 1) n + 4 + scheduleTail f 1 n)
    rw [ih]
    simp only [scheduleTail]
    rw [Nat.add_comm 1 n]
    omega

theorem schedulePoint_succ (f : Nat -> Nat) (n : Nat) :
    schedulePoint f (n + 1) = addPoint (spacedShift (f 0)) (schedulePoint (scheduleTail f 1) n) := by
  apply Prod.ext <;>
    simp only [schedulePoint, scheduleOffset, scheduleDistance_tail, addPoint, chainHead, spacedShift,
      Int.natCast_add] <;> omega

theorem scheduleTime_tail (f : Nat -> Nat) (n : Nat) :
    scheduleTime f (n + 1) = spacedPeriod (f 0) + scheduleTime (scheduleTail f 1) n := by
  induction n with
  | zero => simp [scheduleTime]
  | succ n ih =>
    change scheduleTime f (n + 1) + spacedPeriod (f (n + 1)) =
      spacedPeriod (f 0) + (scheduleTime (scheduleTail f 1) n + spacedPeriod (scheduleTail f 1 n))
    rw [ih]
    simp only [scheduleTail]
    rw [Nat.add_comm 1 n]
    omega

theorem scheduleMask_split (f : Nat -> Nat) :
    scheduleMask f = prependObstacles (f 0) (scheduleMask (scheduleTail f 1)) := by
  funext p
  have he : scheduleMask f p = true ↔ prependObstacles (f 0) (scheduleMask (scheduleTail f 1)) p = true := by
    simp only [scheduleMask_iff, prependObstacles, Bool.or_eq_true, decide_eq_true_eq, shiftedObstacles]
    constructor
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
        right
        exact ⟨n, by rw [schedulePoint_succ, subPoint_addPoint]⟩
    · rintro (hp | hp)
      · exact ⟨0, hp⟩
      · obtain ⟨n, hn⟩ := hp
        exact ⟨n + 1, by rw [schedulePoint_succ, ← hn, addPoint_subPoint]⟩
  cases h1 : scheduleMask f p <;> cases h2 : prependObstacles (f 0) (scheduleMask (scheduleTail f 1)) p <;> simp_all

theorem scheduleOffset_succ (f : Nat -> Nat) (n : Nat) :
    scheduleOffset f (n + 1) = addPoint (scheduleOffset f n) (spacedShift (f n)) := by
  apply Prod.ext <;> simp only [scheduleOffset, scheduleDistance, addPoint, spacedShift, Int.natCast_add] <;> omega

theorem scheduleTail_succ (f : Nat -> Nat) (n : Nat) :
    scheduleTail (scheduleTail f n) 1 = scheduleTail f (n + 1) := by
  funext j
  simp only [scheduleTail, Nat.add_assoc]

theorem scheduleTime_ge (f : Nat -> Nat) (n : Nat) : n <= scheduleTime f n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [scheduleTime, spacedPeriod]; omega

/-- The complete normalized state agrees with the next unused part of the schedule. -/
theorem schedule_entries (f : Nat -> Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (scheduleMask f) highwaySeed.toState)) (n : Nat) :
    AgreesBelow (weight (scheduleOffset f n)) (run s (scheduleTime f n))
      (translate (scheduleOffset f n) (perturb (scheduleMask (scheduleTail f n)) highwaySeed.toState)) := by
  induction n with
  | zero =>
    have hf : scheduleTail f 0 = f := by funext j; simp [scheduleTail]
    simpa only [scheduleTime, scheduleOffset, scheduleDistance, hf, Int.natCast_zero, Int.mul_zero,
      translate_zero, run_zero, weight, Int.zero_add] using h
  | succ n ih =>
    rw [scheduleMask_split (scheduleTail f n), scheduleTail_succ] at ih
    have hh := variableBlock_entry_translated (scheduleMask_ahead (scheduleTail f (n + 1)))
      (f n) (scheduleOffset f n) ih
    rw [← run_add, ← scheduleOffset_succ] at hh
    exact hh

/-- All obstacles are present from time zero; no finite seed is added to the board. -/
noncomputable def scheduledObstacles (f : Nat -> Nat) : State :=
  perturb (fun p => scheduleMask f (subPoint p chainOrigin)) blank

theorem scheduledObstacles_black (f : Nat -> Nat) (p : Point) :
    (scheduledObstacles f).board p = true ↔ exists n : Nat,
      p = (-68 - 2 * (scheduleDistance f n : Int), -42 - 2 * (scheduleDistance f n : Int)) := by
  simp only [scheduledObstacles, perturb, blank, Bool.false_xor, scheduleMask_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Prod.ext <;> simp only [subPoint, chainOrigin, schedulePoint, scheduleOffset, addPoint, chainHead,
      Prod.mk.injEq] at hn ⊢ <;> omega
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    apply Prod.ext <;> simp [subPoint, chainOrigin, schedulePoint, scheduleOffset, addPoint, chainHead] <;> omega

theorem scheduledObstacles_entries (f : Nat -> Nat) (n : Nat) :
    AgreesBelow (weight (addPoint chainOrigin (scheduleOffset f n)))
      (run (scheduledObstacles f) (12496 + scheduleTime f n))
      (translate (addPoint chainOrigin (scheduleOffset f n))
        (perturb (scheduleMask (scheduleTail f n)) highwaySeed.toState)) := by
  have he0 : AgreesBelow (weight chainOrigin) (run (scheduledObstacles f) 12496)
      (translate chainOrigin (perturb (scheduleMask f) highwaySeed.toState)) :=
    aheadMask_blank_entry (scheduleMask_ahead f)
  have he := he0.unshift
  have hh := (schedule_entries f he n).translate chainOrigin
  rw [translate_run, translate_add, addPoint_subPoint, translate_zero, ← run_add, translate_add] at hh
  simpa only [weight_addPoint, Int.add_comm] using hh

theorem scheduleDistance_ge (f : Nat -> Nat) (n : Nat) : n <= scheduleDistance f n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [scheduleDistance]; omega

theorem scheduledObstacles_not_finite (f : Nat -> Nat) : ¬FiniteSupport (scheduledObstacles f).board := by
  rintro ⟨cells, hc⟩
  let n := (-weightFloor cells).toNat + 1
  let p : Point := (-68 - 2 * (scheduleDistance f n : Int), -42 - 2 * (scheduleDistance f n : Int))
  have hp := (scheduledObstacles_black f p).mpr ⟨n, rfl⟩
  have hw := weightFloor_le (hc p hp)
  have hn := scheduleDistance_ge f n
  dsimp [p, weight] at hw
  have he : weightFloor cells <= -110 - 4 * (n : Int) := by omega
  dsimp [n] at he
  omega

end LangtonsAnt
