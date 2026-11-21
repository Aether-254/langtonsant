import VariableObstacleBlock

namespace LangtonsAnt

/-- Each entry specifies the extra standard cycles between two successive obstacles. -/
def variableCells : List Nat -> List Point
  | [] => [chainHead]
  | k :: ks => chainHead :: (variableCells ks).map (addPoint (spacedShift k))

def variableMask (ks : List Nat) : Board := fun p => decide (p ∈ variableCells ks)

def variableRecovery : List Nat -> Nat
  | [] => 548
  | k :: ks => spacedPeriod k + variableRecovery ks

theorem variableCells_length (ks : List Nat) : (variableCells ks).length = ks.length + 1 := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [variableCells, List.length_cons, List.length_map, ih]

theorem variableMask_ahead (ks : List Nat) : AheadMask (variableMask ks) := by
  intro p hp
  have hm : p ∈ variableCells ks := by simpa only [variableMask, decide_eq_true_eq] using hp
  induction ks generalizing p with
  | nil =>
    have he : p = chainHead := by simpa only [variableCells, List.mem_singleton] using hm
    exact ⟨0, he⟩
  | cons k ks ih =>
    simp only [variableCells, List.mem_cons, List.mem_map] at hm
    rcases hm with hm | ⟨q, hq, he⟩
    · exact ⟨0, hm⟩
    · obtain ⟨i, hi⟩ := ih q (by simpa only [variableMask, decide_eq_true_eq] using hq) hq
      refine ⟨k + 4 + i, ?_⟩
      rw [← he, hi]
      apply Prod.ext <;> simp only [addPoint, spacedShift, Int.natCast_add] <;> omega

theorem variableMask_cons (k : Nat) (ks : List Nat) :
    variableMask (k :: ks) = prependObstacles k (variableMask ks) := by
  funext p
  have he : p ∈ variableCells (k :: ks) ↔ p = chainHead ∨ subPoint p (spacedShift k) ∈ variableCells ks := by
    simp only [variableCells, List.mem_cons, List.mem_map]
    constructor
    · rintro (h | ⟨q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (by simpa only [subPoint_addPoint] using hq)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨subPoint p (spacedShift k), h, addPoint_subPoint _ _⟩
  simp only [variableMask, prependObstacles, shiftedObstacles, he]
  by_cases hh : p = chainHead <;> by_cases ht : subPoint p (spacedShift k) ∈ variableCells ks <;> simp [hh, ht]

theorem variableCells_distinct (ks : List Nat) : (variableCells ks).Nodup := by
  induction ks with
  | nil => simp [variableCells]
  | cons k ks ih =>
    rw [variableCells, List.nodup_cons]
    constructor
    · intro hh
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hh
      have hm : shiftedObstacles k (variableMask ks) chainHead = true := by
        rw [← he]
        simpa only [shiftedObstacles, subPoint_addPoint, variableMask, decide_eq_true_eq] using hp
      have hg := (shiftedObstacles_geometry (variableMask_ahead ks) k hm).2.1
      change (-4 : Int) <= -12 - 2 * (k : Int) at hg
      omega
    · apply ih.map
      intro p q hne he
      apply hne
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      apply Prod.ext <;> simp only [addPoint] at hx hy ⊢ <;> omega

theorem variableMask_nil : variableMask [] = prependObstacles 0 (fun _ => false) := by
  funext p
  simp only [variableMask, variableCells, List.mem_singleton, prependObstacles, shiftedObstacles, Bool.or_false]

theorem variableRecovery_formula (ks : List Nat) :
    variableRecovery ks = 548 * (ks.length + 1) + 104 * ks.sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [variableRecovery, ih, spacedPeriod, List.length_cons, List.sum_cons, Nat.mul_add]
    omega

theorem variableMask_standard (ks : List Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (variableMask ks) highwaySeed.toState)) :
    StandardHighwayFrom s (variableRecovery ks) (-2, -2) := by
  induction ks generalizing s with
  | nil =>
    rw [variableMask_nil] at h
    have ha : AheadMask (fun _ => false) := by intro p hp; contradiction
    have he := variableBlock_entry ha 0 h
    have hz : perturb (fun _ => false) highwaySeed.toState = highwaySeed.toState := by simp [perturb]
    rw [hz] at he
    exact standard_highway_of_entry (spacedShift 0) he
  | cons k ks ih =>
    rw [variableMask_cons] at h
    have hr := ih (variableBlock_step (variableMask_ahead ks) k h)
    have ht := hr.translate (spacedShift k)
    rw [translate_add, addPoint_subPoint, translate_zero] at ht
    exact ht.of_run

/-- A finite, nonempty chain with freely chosen even gaps at least eight, installed at time zero. -/
def variableObstacles (ks : List Nat) : State :=
  perturb (fun p => variableMask ks (subPoint p chainOrigin)) blank

theorem variableObstacles_black (ks : List Nat) (p : Point) :
    (variableObstacles ks).board p = true ↔ p ∈ (variableCells ks).map (addPoint chainOrigin) := by
  simp only [variableObstacles, perturb, blank, Bool.false_xor, variableMask, decide_eq_true_eq, List.mem_map]
  constructor
  · intro h
    exact ⟨subPoint p chainOrigin, h, addPoint_subPoint _ _⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [subPoint_addPoint] using hq

theorem variableObstacles_finite (ks : List Nat) : FiniteSupport (variableObstacles ks).board :=
  ⟨(variableCells ks).map (addPoint chainOrigin), fun p hp => (variableObstacles_black ks p).mp hp⟩

theorem variableObstacles_standard (ks : List Nat) :
    StandardHighwayFrom (variableObstacles ks) (12496 + 548 * (ks.length + 1) + 104 * ks.sum) (-2, -2) := by
  have he := (aheadMask_blank_entry (variableMask_ahead ks)).translate (64, 38)
  rw [translate_add] at he
  have hz : addPoint (64, 38) chainOrigin = (0, 0) := by decide
  rw [hz, translate_zero] at he
  have hh : AgreesBelow 0 (translate (64, 38) (run (variableObstacles ks) 12496))
      (perturb (variableMask ks) highwaySeed.toState) := he
  have hs := (variableMask_standard ks hh).translate chainOrigin
  rw [translate_add] at hs
  have hz' : addPoint chainOrigin (64, 38) = (0, 0) := by decide
  rw [hz', translate_zero] at hs
  have ht := hs.of_run
  simpa only [variableRecovery_formula, Nat.add_assoc] using ht

end LangtonsAnt
