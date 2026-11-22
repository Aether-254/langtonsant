import RecordPair

/-! Stable time and visit rank for full drift `(1, -1)`. -/
namespace LangtonsAnt

def layer (p : Point) : Int := weight p
def lift (p : Point) : Int := p.1

def stableTime (P : Nat) (w : Nat → Bool) (i : Nat) : Int :=
  (i : Int) - (P : Int) * (wordPos w i).1

def layerPhases (P : Nat) (w : Nat → Bool) (L : Int) : List Nat :=
  (List.range P).filter (fun i => decide (layer (wordPos w i) = L))

/-- Zero-based rank, counting all earlier visits in the translation class. -/
def stableRank (P : Nat) (w : Nat → Bool) (i : Nat) : Nat :=
  (priorPhases P w i).length

theorem mem_layerPhases {P i : Nat} {w : Nat → Bool} {L : Int} :
    i ∈ layerPhases P w L ↔ i < P ∧ layer (wordPos w i) = L := by
  simp [layerPhases]

theorem unitDiagonal_decomposition (p : Point) :
    p = addPoint (0, layer p) (scalePoint (1, -1) (lift p)) := by
  apply Prod.ext <;> simp [addPoint, scalePoint, layer, weight, lift] <;> omega

theorem unitDiagonal_same_layer_iff (p q : Point) :
    layer p = layer q ↔ ∃ k : Int, p = addPoint q (scalePoint (1, -1) k) := by
  constructor
  · intro h
    refine ⟨p.1 - q.1, ?_⟩
    apply Prod.ext <;> simp only [addPoint, scalePoint, Int.mul_one, Int.mul_neg] <;> simp only [layer, weight] at h <;> omega
  · rintro ⟨k, rfl⟩
    simp [layer, weight, addPoint, scalePoint] <;> omega

/-- Integer time uniquely determines the phase and period. -/
theorem biTime_injective {P i j : Nat} {k l : Int} (hi : i < P) (hj : j < P)
    (h : k * (P : Int) + i = l * (P : Int) + j) : k = l ∧ i = j := by
  have hk : k = l := by
    by_cases hkl : k < l
    · have hm := Int.mul_le_mul_of_nonneg_right (show k + 1 ≤ l by omega)
        (show 0 ≤ (P : Int) by omega)
      rw [Int.add_mul, Int.one_mul] at hm
      omega
    · by_cases hlk : l < k
      · have hm := Int.mul_le_mul_of_nonneg_right (show l + 1 ≤ k by omega)
          (show 0 ≤ (P : Int) by omega)
        rw [Int.add_mul, Int.one_mul] at hm
        omega
      · omega
  exact ⟨hk, by rw [hk] at h; omega⟩

theorem stableTime_injective {P i j : Nat} {w : Nat → Bool}
    (hi : i < P) (hj : j < P) (h : stableTime P w i = stableTime P w j) : i = j := by
  apply (biTime_injective (k := -(wordPos w i).1) (l := -(wordPos w j).1) hi hj ?_).2
  simp only [Int.neg_mul, Int.mul_comm (wordPos w i).1, Int.mul_comm (wordPos w j).1]
  unfold stableTime at h
  omega

theorem mem_priorPhases_iff_stableTime {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    j ∈ priorPhases P w i ↔ j < P ∧ layer (wordPos w j) = layer (wordPos w i) ∧
      stableTime P w j < stableTime P w i := by
  have hv : wordDrift P w ≠ (0, 0) := by rw [hd]; decide
  by_cases hj : j < P
  · rw [mem_priorPhases_iff_integer_period hv hi hj]
    constructor
    · rintro ⟨k, ht, hp⟩
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      simp only [biPeriodicPos, hd, addPoint, scalePoint, Int.mul_one,
        Int.mul_neg] at hx hy
      have hk : k = (wordPos w i).1 - (wordPos w j).1 := by omega
      rw [hk, Int.sub_mul, Int.mul_comm (wordPos w i).1,
        Int.mul_comm (wordPos w j).1] at ht
      exact ⟨hj, by simp only [layer, weight]; omega, by unfold stableTime; omega⟩
    · rintro ⟨_, hl, ht⟩
      refine ⟨(wordPos w i).1 - (wordPos w j).1, ?_, ?_⟩
      · simp only [Int.sub_mul, Int.mul_comm (wordPos w i).1,
          Int.mul_comm (wordPos w j).1]
        unfold stableTime at ht
        omega
      · apply Prod.ext <;> simp only [biPeriodicPos, hd, addPoint, scalePoint,
          Int.mul_one, Int.mul_neg] <;> simp only [layer, weight] at hl <;> omega
  · rw [mem_priorPhases hv]
    simp [hj]

theorem ConsistentWord.stableRank_color {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hi : i < P) :
    w i = decide (stableRank P w i % 2 = 1) := h.2.2 i hi

theorem priorPhases_eq_stableTime_filter {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    priorPhases P w i = (layerPhases P w (layer (wordPos w i))).filter
      (fun j => decide (stableTime P w j < stableTime P w i)) := by
  unfold priorPhases layerPhases
  rw [List.filter_filter]
  apply List.filter_congr
  intro j hj
  apply Bool.eq_iff_iff.mpr
  have hh := mem_priorPhases_iff_stableTime (j := j) hd hi
  simpa [priorPhases, List.mem_range.mp hj, and_comm] using hh

theorem stableRank_lt_of_stableTime_lt {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hl : layer (wordPos w i) = layer (wordPos w j))
    (ht : stableTime P w i < stableTime P w j) :
    stableRank P w i < stableRank P w j := by
  have hnot : i ∉ priorPhases P w i := by
    rw [mem_priorPhases_iff_stableTime hd hi]
    omega
  have hnd : (i :: priorPhases P w i).Nodup :=
    List.nodup_cons.mpr ⟨hnot, priorPhases_nodup P w i⟩
  have hs : i :: priorPhases P w i ⊆ priorPhases P w j := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact (mem_priorPhases_iff_stableTime hd hj).mpr ⟨hi, hl, ht⟩
    · rcases (mem_priorPhases_iff_stableTime hd hi).mp hk with ⟨hkP, hkl, hkt⟩
      exact (mem_priorPhases_iff_stableTime hd hj).mpr ⟨hkP, hkl.trans hl, by omega⟩
  have := hnd.length_le_of_subset hs
  simpa only [List.length_cons, stableRank, Nat.succ_le_iff] using this

theorem stableRank_lt_iff_stableTime_lt {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hl : layer (wordPos w i) = layer (wordPos w j)) :
    stableRank P w i < stableRank P w j ↔ stableTime P w i < stableTime P w j := by
  refine ⟨?_, stableRank_lt_of_stableTime_lt hd hi hj hl⟩
  intro hr
  by_cases ht : stableTime P w i < stableTime P w j
  · exact ht
  · by_cases he : stableTime P w i = stableTime P w j
    · have := stableTime_injective hi hj he
      subst j
      omega
    · have := stableRank_lt_of_stableTime_lt hd hj hi hl.symm (by omega)
      omega

theorem stableRank_succ_iff {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hl : layer (wordPos w i) = layer (wordPos w j)) :
    stableRank P w j = stableRank P w i + 1 ↔
      stableTime P w i < stableTime P w j ∧
      ¬ ∃ k, k < P ∧ layer (wordPos w k) = layer (wordPos w i) ∧
        stableTime P w i < stableTime P w k ∧ stableTime P w k < stableTime P w j := by
  constructor
  · intro hr
    refine ⟨(stableRank_lt_iff_stableTime_lt hd hi hj hl).mp (by omega), ?_⟩
    rintro ⟨k, hk, hkl, hik, hkj⟩
    have := stableRank_lt_of_stableTime_lt hd hi hk hkl.symm hik
    have := stableRank_lt_of_stableTime_lt hd hk hj (hkl.trans hl) hkj
    omega
  · rintro ⟨ht, hgap⟩
    have hnot : i ∉ priorPhases P w i := by
      rw [mem_priorPhases_iff_stableTime hd hi]
      omega
    have hp : (priorPhases P w j).Perm (i :: priorPhases P w i) := by
      apply (List.perm_ext_iff_of_nodup (priorPhases_nodup P w j)
        (List.nodup_cons.mpr ⟨hnot, priorPhases_nodup P w i⟩)).mpr
      intro k
      rw [List.mem_cons, mem_priorPhases_iff_stableTime hd hj,
        mem_priorPhases_iff_stableTime hd hi]
      constructor
      · rintro ⟨hk, hkl, hkt⟩
        by_cases he : stableTime P w k = stableTime P w i
        · exact Or.inl (stableTime_injective hk hi he)
        · right
          refine ⟨hk, hkl.trans hl.symm, ?_⟩
          have : ¬ stableTime P w i < stableTime P w k :=
            fun h => hgap ⟨k, hk, hkl.trans hl.symm, h, hkt⟩
          omega
      · rintro (rfl | ⟨hk, hkl, hkt⟩)
        · exact ⟨hi, hl, ht⟩
        · exact ⟨hk, hkl.trans hl, by omega⟩
    exact hp.length_eq

/-- A finite segment of consecutive integer times, with explicit phase and seam carry.
The bounds and `time_step` force precisely cyclic succession, including at the seam.
No bound on length relative to the period is imposed. -/
structure ContinuousPhasePath (P len : Nat) where
  phase : Nat → Nat
  period : Nat → Int
  phase_lt : ∀ r, r ≤ len → phase r < P
  time_step : ∀ r, r < len →
    period (r + 1) * (P : Int) + phase (r + 1) =
      period r * (P : Int) + phase r + 1

namespace ContinuousPhasePath

/-- The canonical segment at natural times `start, ..., start + len`.
Natural quotient/remainder is used only here; the core interface uses no integer division. -/
def ofStart {P : Nat} (hP : 0 < P) (start len : Nat) : ContinuousPhasePath P len where
  phase r := (start + r) % P
  period r := ((start + r) / P : Nat)
  phase_lt r _ := Nat.mod_lt _ hP
  time_step r _ := by
    have h0 := Nat.div_add_mod (start + r) P
    have h1 := Nat.div_add_mod (start + (r + 1)) P
    have hc0 : (((start + r) / P : Nat) : Int) * (P : Int) +
        (((start + r) % P : Nat) : Int) = (start + r : Nat) := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using h0)
    have hc1 : (((start + (r + 1)) / P : Nat) : Int) * (P : Int) +
        (((start + (r + 1)) % P : Nat) : Int) = (start + (r + 1) : Nat) := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using h1)
    omega

def pos {P len : Nat} (p : ContinuousPhasePath P len) (w : Nat → Bool)
    (r : Nat) : Point := biPeriodicPos P w (p.period r) (p.phase r)

theorem pos_ofStart {P : Nat} {w : Nat → Bool} (hP : 0 < P)
    (hd : (wordTrace w P).2 = .north) (start len r : Nat) :
    (ofStart hP start len).pos w r = wordPos (repeatWord P w) (start + r) := by
  rw [repeatWord_position hd]
  have he := congrArg Prod.fst (repeatWord_trace w
    (Nat.le_of_lt (Nat.mod_lt (start + r) hP)))
  change wordPos (repeatWord P w) ((start + r) % P) = wordPos w ((start + r) % P) at he
  rw [he]
  rfl

theorem time_eq {P len : Nat} (p : ContinuousPhasePath P len) {r : Nat} (hr : r ≤ len) :
    p.period r * (P : Int) + p.phase r =
      p.period 0 * (P : Int) + p.phase 0 + (r : Int) := by
  induction r with
  | zero => omega
  | succ r ih =>
    have := p.time_step r (by omega)
    have := ih (by omega)
    push_cast
    omega

theorem successor {P len : Nat} (p : ContinuousPhasePath P len)
    {r : Nat} (hr : r < len) :
    (p.phase (r + 1) = p.phase r + 1 ∧ p.period (r + 1) = p.period r) ∨
    (p.phase r + 1 = P ∧ p.phase (r + 1) = 0 ∧
      p.period (r + 1) = p.period r + 1) := by
  have hcur := p.phase_lt r (by omega)
  have hnxt := p.phase_lt (r + 1) (by omega)
  have ht := p.time_step r hr
  by_cases h : p.phase r + 1 < P
  · have he : p.period (r + 1) * (P : Int) + p.phase (r + 1) =
        p.period r * (P : Int) + (p.phase r + 1 : Nat) := by omega
    have he := biTime_injective hnxt h he
    exact Or.inl ⟨he.2, he.1⟩
  · have he : p.period (r + 1) * (P : Int) + p.phase (r + 1) =
        (p.period r + 1) * (P : Int) + (0 : Nat) := by
      rw [Int.add_mul, Int.one_mul]
      omega
    have he := biTime_injective hnxt (show 0 < P by omega) he
    exact Or.inr ⟨by omega, he.2, he.1⟩

/-- The integer-time interface lifts to consecutive physical moves. -/
theorem pos_step {P len : Nat} {w : Nat → Bool} (p : ContinuousPhasePath P len)
    {r : Nat} (hr : r < len) :
    p.pos w (r + 1) = move (p.pos w r)
      (turn (w (p.phase r)) (wordTrace w (p.phase r)).2) := by
  have move_translate (a b : Point) (d : Direction) :
      move (addPoint a b) d = addPoint (move a d) b := by
    cases d <;> apply Prod.ext <;> simp [move, addPoint] <;> omega
  rcases p.successor hr with ⟨hp, hk⟩ | ⟨hp, hz, hk⟩
  · simp only [pos, biPeriodicPos, hp, hk, wordPos, wordTrace]
    rw [move_translate]
  · have hmove : move (wordPos w (p.phase r))
        (turn (w (p.phase r)) (wordTrace w (p.phase r)).2) = wordDrift P w := by
      change wordPos w (p.phase r + 1) = wordDrift P w
      rw [hp]
      rfl
    simp only [pos, biPeriodicPos, hz, hk]
    rw [move_translate, hmove]
    apply Prod.ext <;> simp [wordPos, wordTrace, addPoint, scalePoint, Int.add_mul] <;> omega

theorem heading_step {P len : Nat} {w : Nat → Bool} (p : ContinuousPhasePath P len)
    (hd : (wordTrace w P).2 = .north) {r : Nat} (hr : r < len) :
    (wordTrace w (p.phase (r + 1))).2 =
      turn (w (p.phase r)) (wordTrace w (p.phase r)).2 := by
  rcases p.successor hr with ⟨hp, _⟩ | ⟨hp, hz, _⟩
  · rw [hp, wordTrace]
  · have hh : (wordTrace w (p.phase r + 1)).2 = .north := by rw [hp, hd]
    simpa only [hz, wordTrace] using hh.symm

theorem stableTime_eq {P len : Nat} {w : Nat → Bool} (p : ContinuousPhasePath P len)
    (hd : wordDrift P w = (1, -1)) (r : Nat) :
    stableTime P w (p.phase r) = p.period r * (P : Int) + p.phase r -
      (P : Int) * (p.pos w r).1 := by
  simp only [stableTime, pos, biPeriodicPos, hd, addPoint, scalePoint, Int.mul_one,
    Int.mul_add, Int.mul_comm (P : Int) (p.period r)]
  omega

/-- The seam-corrected key difference; displacement is the lifted physical displacement. -/
theorem stableTime_difference {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = (1, -1)) {δ : Int}
    (hdisp : p.pos w len = addPoint (p.pos w 0) (scalePoint (1, -1) δ)) :
    stableTime P w (p.phase len) - stableTime P w (p.phase 0) =
      (len : Int) - (P : Int) * δ := by
  have hx := congrArg Prod.fst hdisp
  simp only [addPoint, scalePoint, Int.mul_one] at hx
  rw [p.stableTime_eq hd len, p.stableTime_eq hd 0, hx, Int.mul_add]
  have := p.time_eq (Nat.le_refl len)
  omega

theorem return_stableTime {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = (1, -1))
    (hret : p.pos w len = p.pos w 0) :
    stableTime P w (p.phase len) = stableTime P w (p.phase 0) + (len : Int) := by
  have hh := p.stableTime_difference hd (δ := 0) (by simpa [scalePoint] using hret)
  omega

theorem return_phase_ne {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = (1, -1))
    (hlen : 0 < len) (hret : p.pos w len = p.pos w 0) : p.phase len ≠ p.phase 0 := by
  intro he
  have := p.return_stableTime hd hret
  rw [he] at this
  omega

theorem layer_pos {P len : Nat} {w : Nat → Bool} (p : ContinuousPhasePath P len)
    (hd : wordDrift P w = (1, -1)) (r : Nat) :
    layer (p.pos w r) = layer (wordPos w (p.phase r)) := by
  simp [pos, biPeriodicPos, hd, layer, weight, addPoint, scalePoint]
  omega

/-- Completeness of stable-time visits inside a continuous path. -/
theorem visit_of_stableTime {P len j r : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = (1, -1))
    (hj : j < P) (hr : r ≤ len)
    (hl : layer (wordPos w j) = layer (wordPos w (p.phase 0)))
    (ht : stableTime P w j = stableTime P w (p.phase 0) + (r : Int)) :
    p.pos w r = p.pos w 0 := by
  let k : Int := p.period 0 + (wordPos w (p.phase 0)).1 - (wordPos w j).1
  have htime : k * (P : Int) + j = p.period r * (P : Int) + p.phase r := by
    dsimp [k]
    rw [Int.sub_mul, Int.add_mul, Int.mul_comm (wordPos w (p.phase 0)).1,
      Int.mul_comm (wordPos w j).1]
    have := p.time_eq hr
    unfold stableTime at ht
    omega
  have he := biTime_injective hj (p.phase_lt r hr) htime
  change biPeriodicPos P w (p.period r) (p.phase r) = _
  rw [← he.1, ← he.2]
  apply Prod.ext <;>
    simp only [biPeriodicPos, pos, hd, addPoint, scalePoint, Int.mul_one, Int.mul_neg] <;>
    dsimp [k] <;> simp only [layer, weight] at hl <;> omega

/-- A first physical return advances stable rank by exactly one. -/
theorem firstReturn_rank {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) (hd : wordDrift P w = (1, -1))
    (hlen : 0 < len) (hret : p.pos w len = p.pos w 0)
    (hfirst : ∀ r, 0 < r → r < len → p.pos w r ≠ p.pos w 0) :
    stableRank P w (p.phase len) = stableRank P w (p.phase 0) + 1 := by
  have hkey := p.return_stableTime hd hret
  have hl : layer (wordPos w (p.phase 0)) = layer (wordPos w (p.phase len)) := by
    rw [← p.layer_pos hd 0, ← p.layer_pos hd len, hret]
  apply (stableRank_succ_iff hd (p.phase_lt 0 (by omega))
    (p.phase_lt len (by omega)) hl).mpr
  refine ⟨by omega, ?_⟩
  rintro ⟨j, hj, hjl, ht0, htlen⟩
  let r := (stableTime P w j - stableTime P w (p.phase 0)).toNat
  have hr : (r : Int) = stableTime P w j - stableTime P w (p.phase 0) := by
    dsimp [r]
    omega
  exact hfirst r (by omega) (by omega)
    (p.visit_of_stableTime hd hj (by omega) hjl (by omega))

end ContinuousPhasePath

end LangtonsAnt

