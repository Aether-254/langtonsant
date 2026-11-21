import DelayedRecovery
import MaskedAgreement

namespace LangtonsAnt

def chainShift : Point := (-8, -8)
def chainHead : Point := (-4, -4)

def chainCells : Nat -> List Point
  | 0 => []
  | n + 1 => chainHead :: (chainCells n).map (addPoint chainShift)

def chainMask (n : Nat) : Board := fun p => decide (p ∈ chainCells n)
def chainTail (n : Nat) : Board := fun p => chainMask n (subPoint p chainShift)

def chainPoint (i : Nat) : Point := (-4 - 8 * (i : Int), -4 - 8 * (i : Int))

theorem chainCells_eq_range (n : Nat) : chainCells n = (List.range n).map chainPoint := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chainCells, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hf : (fun i => addPoint chainShift (chainPoint i)) = fun i => chainPoint (i + 1) := by
      funext i
      apply Prod.ext <;> simp [chainPoint, chainShift, addPoint] <;> omega
    change chainHead :: ((List.range n).map (fun i => addPoint chainShift (chainPoint i))) = _
    rw [hf]
    simp only [List.map_map]
    rfl

theorem chainCells_mem (n : Nat) (p : Point) :
    p ∈ chainCells n ↔ exists i, i < n ∧ p = chainPoint i := by
  simp only [chainCells_eq_range, List.mem_map, List.mem_range, eq_comm]

theorem chainPoint_injective {i j : Nat} (h : chainPoint i = chainPoint j) : i = j := by
  have hx := congrArg Prod.fst h
  simp only [chainPoint] at hx
  omega

theorem chainCells_length (n : Nat) : (chainCells n).length = n := by
  simp [chainCells_eq_range]

theorem chainCells_weight {n : Nat} {p : Point} (h : p ∈ chainCells n) : weight p <= -8 := by
  induction n generalizing p with
  | zero => simp [chainCells] at h
  | succ n ih =>
    simp only [chainCells, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨q, hq, he⟩
    · rw [h]; decide
    · rw [← he, weight_addPoint]
      have hb := ih hq
      change -16 + weight q <= -8
      omega

theorem chainTail_weight {n : Nat} {p : Point} (h : chainTail n p = true) : weight p <= -24 := by
  have hm : subPoint p chainShift ∈ chainCells n := by simpa [chainTail, chainMask] using h
  have hw := chainCells_weight hm
  simp only [weight, subPoint, chainShift] at hw ⊢
  omega

theorem chainCells_mem_succ (n : Nat) (p : Point) :
    p ∈ chainCells (n + 1) ↔ p = chainHead ∨ subPoint p chainShift ∈ chainCells n := by
  simp only [chainCells, List.mem_cons]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp h
      rw [← he, subPoint_addPoint]
      exact Or.inr hq
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_map.mpr ⟨subPoint p chainShift, h, addPoint_subPoint _ _⟩)

theorem chainMask_succ (n : Nat) (s : State) :
    perturb (chainMask (n + 1)) s = perturb (chainTail n) (flipCell s chainHead) := by
  have hb : (fun p => s.board p ^^ chainMask (n + 1) p) =
      fun p => flip s.board chainHead p ^^ chainTail n p := by
    funext p
    have ht : chainTail n chainHead = false := by
      cases hc : chainTail n chainHead
      · rfl
      · have hw := chainTail_weight hc
        change -8 <= -24 at hw
        omega
    by_cases hp : p = chainHead
    · subst p
      simp only [chainMask, chainCells_mem_succ, true_or, decide_true, flip_same, ht, Bool.xor_false]
      cases s.board chainHead <;> rfl
    · simp only [chainMask, chainCells_mem_succ, hp, false_or, flip_other _ hp]
      rfl
  simp only [perturb, flipCell, hb]

def chainCollisionSeed : FiniteState :=
  { highwaySeed with black := toggleCells highwaySeed.black chainHead }

theorem chainCollisionSeed_toState : chainCollisionSeed.toState = flipCell highwaySeed.toState chainHead :=
  highwaySeed.toState_flip chainHead

def checkWeightRange (lo hi : Int) : Nat -> FiniteState -> Bool
  | 0, _ => true
  | n + 1, s => decide (lo <= weight s.pos ∧ weight s.pos <= hi) &&
      checkWeightRange lo hi n s.step

theorem checkWeightRange_sound {lo hi : Int} {n : Nat} {s : FiniteState}
    (h : checkWeightRange lo hi n s = true) :
    forall j, j < n -> lo <= weight (run s.toState j).pos ∧ weight (run s.toState j).pos <= hi := by
  induction n generalizing s with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkWeightRange, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j =>
      have hh := ih h.2 j (by omega)
      rw [FiniteState.toState_step] at hh
      change _ <= weight (run (run s.toState 1) j).pos ∧ weight (run (run s.toState 1) j).pos <= _ at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 j] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem chainCollision_check :
    (checkWeightRange (-23) 0 548 chainCollisionSeed &&
      checkAgreement (-16) (chainCollisionSeed.run 548) (highwaySeed.translate chainShift)) = true := by
  decide +kernel

theorem chainCollision_range (j : Nat) (hj : j < 548) :
    -23 <= weight (run chainCollisionSeed.toState j).pos ∧
      weight (run chainCollisionSeed.toState j).pos <= 0 := by
  have h := chainCollision_check
  simp only [Bool.and_eq_true] at h
  exact checkWeightRange_sound h.1 j hj

set_option maxRecDepth 100000 in
theorem chainCollision_entry :
    AgreesBelow (-16) (run chainCollisionSeed.toState 548) (translate chainShift highwaySeed.toState) := by
  have h := chainCollision_check
  simp only [Bool.and_eq_true] at h
  simpa only [FiniteState.toState_run, FiniteState.toState_translate] using checkAgreement_sound h.2

theorem chain_step {n : Nat} {s : State}
    (h : AgreesBelow 0 s (perturb (chainMask (n + 1)) highwaySeed.toState)) :
    AgreesBelow 0 (translate (8, 8) (run s 548)) (perturb (chainMask n) highwaySeed.toState) := by
  rw [chainMask_succ, ← chainCollisionSeed_toState] at h
  have hr := h.run_perturb 548
    (fun j hj => (chainCollision_range j hj).2) (by
      intro j hj
      cases hc : chainTail n (run chainCollisionSeed.toState j).pos
      · rfl
      · have hw := chainTail_weight hc
        have hb := (chainCollision_range j hj).1
        omega)
  have he := chainCollision_entry.perturb (chainTail n)
  have hh := (hr.weaken (by omega : (-16 : Int) <= 0)).trans he
  have ht := hh.translate (8, 8)
  have hsum : addPoint (8, 8) chainShift = (0, 0) := by decide
  have hmask : (fun p => chainTail n (subPoint p (8, 8))) = chainMask n := by
    funext p
    have hp : subPoint (subPoint p (8, 8)) chainShift = p := by
      apply Prod.ext <;> simp [subPoint, chainShift] <;> omega
    simp only [chainTail, hp]
  rw [perturb_translate, translate_add, hsum, translate_zero, hmask] at ht
  exact ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem chainCollision_contact_check : (chainCollisionSeed.run 108).pos = chainHead := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem chainCollision_first_check :
    forall j : Fin 108, (chainCollisionSeed.run j.val).pos ≠ chainHead := by
  decide +kernel

theorem chain_prefix_pos {n : Nat} {s : State}
    (h : AgreesBelow 0 s (perturb (chainMask (n + 1)) highwaySeed.toState))
    (j : Nat) (hj : j <= 548) :
    (run s j).pos = (run chainCollisionSeed.toState j).pos := by
  rw [chainMask_succ, ← chainCollisionSeed_toState] at h
  have hr := h.run_perturb j
    (fun i hi => (chainCollision_range i (by omega)).2) (by
      intro i hi
      cases hc : chainTail n (run chainCollisionSeed.toState i).pos
      · rfl
      · have hw := chainTail_weight hc
        have hb := (chainCollision_range i (by omega)).1
        omega)
  exact hr.pos

set_option maxRecDepth 100000 in
theorem chain_head_contact {n : Nat} {s : State}
    (h : AgreesBelow 0 s (perturb (chainMask (n + 1)) highwaySeed.toState)) :
    (run s 108).pos = chainHead := by
  have hp := chain_prefix_pos h 108 (by decide)
  have he : (chainCollisionSeed.run 108).pos = (run chainCollisionSeed.toState 108).pos :=
    congrArg State.pos (chainCollisionSeed.toState_run 108)
  exact hp.trans (he.symm.trans chainCollision_contact_check)

theorem chain_visits (n : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (chainMask n) highwaySeed.toState)) :
    forall i, i < n -> (run s (548 * i + 108)).pos = chainPoint i := by
  induction n generalizing s with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact chain_head_contact h
    | succ i =>
      have hh := ih (chain_step h) i (by omega)
      rw [translate_run, ← run_add] at hh
      change addPoint (8, 8) (run s (548 + (548 * i + 108))).pos = chainPoint i at hh
      have heq : 548 + (548 * i + 108) = 548 * (i + 1) + 108 := by omega
      rw [heq] at hh
      apply Prod.ext <;> simp only [addPoint, chainPoint, Prod.mk.injEq] at hh ⊢ <;> omega

theorem chain_first_visits (n : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (chainMask n) highwaySeed.toState)) :
    forall i, i < n -> forall j, j < 548 * i + 108 -> (run s j).pos ≠ chainPoint i := by
  induction n generalizing s with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi j hj he
    cases i with
    | zero =>
      have hp := chain_prefix_pos h j (by omega)
      have hr : (chainCollisionSeed.run j).pos = (run chainCollisionSeed.toState j).pos :=
        congrArg State.pos (chainCollisionSeed.toState_run j)
      have hc := chainCollision_first_check ⟨j, by omega⟩
      exact hc (hr.trans (hp.symm.trans he))
    | succ i =>
      by_cases hearly : j < 548
      · have hp := chain_prefix_pos h j (by omega)
        have hb := (chainCollision_range j hearly).1
        rw [← hp, he] at hb
        simp only [chainPoint, weight] at hb
        omega
      · have hh := ih (chain_step h) i (by omega) (j - 548) (by omega)
        apply hh
        rw [translate_run, ← run_add]
        have ht : 548 + (j - 548) = j := by omega
        rw [ht]
        change addPoint (8, 8) (run s j).pos = chainPoint i
        rw [he]
        apply Prod.ext <;> simp [addPoint, chainPoint] <;> omega

theorem chain_standard (n : Nat) {s : State}
    (h : AgreesBelow 0 s (perturb (chainMask n) highwaySeed.toState)) :
    StandardHighwayFrom s (548 * n) (-2, -2) := by
  induction n generalizing s with
  | zero =>
    have he : perturb (chainMask 0) highwaySeed.toState = highwaySeed.toState := by
      simp [chainMask, chainCells, perturb]
    rw [he] at h
    exact highwaySeed_standard.of_agreesBelow h highwaySeed_certificate.all_bounded
  | succ n ih =>
    have hr := ih (chain_step h)
    have ht := hr.translate (-8, -8)
    rw [translate_add] at ht
    have hz : addPoint (-8, -8) (8, 8) = (0, 0) := by decide
    rw [hz, translate_zero] at ht
    have hh := ht.of_run
    have heq : 548 + 548 * n = 548 * (n + 1) := by omega
    simpa only [heq] using hh

end LangtonsAnt
