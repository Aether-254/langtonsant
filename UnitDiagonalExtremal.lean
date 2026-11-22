import UnitDiagonalRank

/-!
# Extremal layers, width, and port identities for unit-diagonal drift `(1, -1)`

Working directly in the word's own frame (`wordTrace` starts at `(0, 0)` facing `.north`)
without cyclic re-normalization, all quantities are expressed relative to `topLayer`:

* **L07**: Each cyclic phase step changes `layer` by `±1` (`.east`, `.north`: `+1`;
  `.south`, `.west`: `-1`), and axis parity locks arrival axis to layer parity:
  `(inDir w i).horizontal = decide (layer (wordPos w i) % 2 = 1)`.
* **L08**: Both extremal layers `topLayer` and `botLayer` contain a unique phase, with
  `stableRank = 0` and white read (`w i = false`); `topLayer` has `inDir = .east`,
  `outDir = .south`, while `botLayer` has `inDir = .west`, `outDir = .north`.
* **L09**: `topLayer` and `botLayer` are odd, `W := topLayer - botLayer` is even and
  positive (`2 ≤ W`), and every intermediate integer layer `L` with
  `botLayer ≤ L ≤ topLayer` is visited by at least one phase `i < P`.
* **L14**: For every phase `i < P`, `beta` satisfies the port XOR identity
  `beta w i = xor (xor (alpha w i) (decide (stableRank P w i % 2 = 1))) (decide (depth P w i % 2 = 1))`,
  and `inDir` (resp. `outDir`) is uniquely determined by `(depth parity, alpha)`
  (resp. `(depth parity, beta)`).
-/

namespace LangtonsAnt

/-! ## Core definitions in the word frame -/

/-- Arrival heading before turning at phase `i`. -/
def inDir (w : Nat → Bool) (i : Nat) : Direction :=
  (wordTrace w i).2

/-- Departure heading after turning at phase `i`. -/
def outDir (w : Nat → Bool) (i : Nat) : Direction :=
  turn (w i) (inDir w i)

/-- Single-step change in `layer = weight` along direction `d`. -/
def layerDelta : Direction → Int
  | .north => 1
  | .east => 1
  | .south => -1
  | .west => -1

/-- Cyclic phase successor modulo `P`. -/
def nextPhase (P i : Nat) : Nat :=
  (i + 1) % P

/-- Cyclic phase predecessor modulo `P`. -/
def prevPhase (P i : Nat) : Nat :=
  if i = 0 then P - 1 else i - 1

/-- Maximum `layer` attained over phases `i < P` (anchored at `layer (wordPos w 0) = 0`). -/
def topLayer (P : Nat) (w : Nat → Bool) : Int :=
  ((List.range P).map (fun i => layer (wordPos w i))).foldl max 0

/-- Minimum `layer` attained over phases `i < P` (anchored at `layer (wordPos w 0) = 0`). -/
def botLayer (P : Nat) (w : Nat → Bool) : Int :=
  ((List.range P).map (fun i => layer (wordPos w i))).foldl min 0

/-- Non-negative depth below `topLayer`. -/
def depth (P : Nat) (w : Nat → Bool) (i : Nat) : Int :=
  topLayer P w - layer (wordPos w i)

/-- Layer span `topLayer - botLayer`. -/
def layerWidth (P : Nat) (w : Nat → Bool) : Int :=
  topLayer P w - botLayer P w

/-- True iff phase `i` arrives from the layer above (`inDir ∈ {south, west}`). -/
def alpha (w : Nat → Bool) (i : Nat) : Bool :=
  decide (inDir w i = .south ∨ inDir w i = .west)

/-- True iff phase `i` leaves to the layer above (`outDir ∈ {north, east}`). -/
def beta (w : Nat → Bool) (i : Nat) : Bool :=
  decide (outDir w i = .north ∨ outDir w i = .east)

/-! ## Private list and order helpers -/

private theorem le_foldl_max_init (init : Int) (l : List Int) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h2 := ih (max init x)
    omega

private theorem mem_le_foldl_max (init : Int) (l : List Int) {x : Int} (hx : x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · have := le_foldl_max_init (max init x) ys
      omega
    · exact ih (max init y) hmem

private theorem foldl_max_mem_or_init (init : Int) (l : List Int) :
    l.foldl max init = init ∨ l.foldl max init ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases ih (max init y) with h | h
    · rw [h]
      by_cases hle : init ≤ y
      · right
        have hmax : max init y = y := by omega
        rw [hmax]
        simp
      · left
        omega
    · exact Or.inr (List.mem_cons_of_mem y h)

private theorem foldl_min_le_init (init : Int) (l : List Int) :
    l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h2 := ih (min init x)
    omega

private theorem foldl_min_le_mem (init : Int) (l : List Int) {x : Int} (hx : x ∈ l) :
    l.foldl min init ≤ x := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · have := foldl_min_le_init (min init x) ys
      omega
    · exact ih (min init y) hmem

private theorem foldl_min_mem_or_init (init : Int) (l : List Int) :
    l.foldl min init = init ∨ l.foldl min init ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases ih (min init y) with h | h
    · rw [h]
      by_cases hle : y ≤ init
      · right
        have hmin : min init y = y := by omega
        rw [hmin]
        simp
      · left
        omega
    · exact Or.inr (List.mem_cons_of_mem y h)

private theorem exists_min_by {α : Type} (f : α → Int) :
    ∀ l : List α, l ≠ [] → ∃ a, a ∈ l ∧ ∀ b, b ∈ l → f a ≤ f b
  | [], h => absurd rfl h
  | [x], _ => ⟨x, by simp, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Int.le_refl _
      · simp at hb⟩
  | x :: y :: xs, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_by f (y :: xs) (List.cons_ne_nil _ _)
    by_cases hxm : f x ≤ f m
    · refine ⟨x, by simp, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Int.le_refl _
      · exact Int.le_trans hxm (hmin b hb)
    · refine ⟨m, List.mem_cons_of_mem x hm, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact hmin b hb

private theorem list_eq_singleton_of_nodup {α : Type} {l : List α} {a : α}
    (hnd : l.Nodup) (ha : a ∈ l) (huniq : ∀ b, b ∈ l → b = a) : l = [a] := by
  cases l with
  | nil => simp at ha
  | cons x xs =>
    have hx : x = a := huniq x (by simp)
    subst hx
    have hxs : xs = [] := by
      cases xs with
      | nil => rfl
      | cons y ys =>
        have hy : y = x := huniq y (by simp)
        subst hy
        have hnot := (List.nodup_cons.mp hnd).1
        simp at hnot
    rw [hxs]

private theorem discrete_ivt (f : Nat → Int)
    (hstep : ∀ k, f (k + 1) = f k + 1 ∨ f (k + 1) = f k - 1)
    (a d : Nat) (L : Int)
    (h : (f a ≤ L ∧ L ≤ f (a + d)) ∨ (f (a + d) ≤ L ∧ L ≤ f a)) :
    ∃ k, a ≤ k ∧ k ≤ a + d ∧ f k = L := by
  induction d with
  | zero =>
    simp only [Nat.add_zero] at h
    exact ⟨a, Nat.le_refl a, by omega, by omega⟩
  | succ d ih =>
    by_cases he : f (a + (d + 1)) = L
    · exact ⟨a + (d + 1), by omega, Nat.le_refl _, he⟩
    · have hs := hstep (a + d)
      rw [show a + d + 1 = a + (d + 1) by omega] at hs
      have h' : (f a ≤ L ∧ L ≤ f (a + d)) ∨ (f (a + d) ≤ L ∧ L ≤ f a) := by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs with hs | hs
        · left; omega
        · left; omega
        · right; omega
        · right; omega
      obtain ⟨k, hka, hkd, hfk⟩ := ih h'
      exact ⟨k, hka, by omega, hfk⟩

/-! ## Basic phase-cycle and layer properties -/

theorem period_pos_of_drift {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) : 0 < P := by
  cases P with
  | zero =>
    simp [wordDrift, wordPos, wordTrace] at hd
  | succ _ => exact Nat.succ_pos _

theorem ConsistentWord.period_pos {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) : 0 < P := by
  cases P with
  | zero =>
    exfalso
    exact h.2.1 (by rfl)
  | succ _ => exact Nat.succ_pos _

theorem layerPhases_nodup (P : Nat) (w : Nat → Bool) (L : Int) :
    (layerPhases P w L).Nodup :=
  List.nodup_range.filter _

theorem nextPhase_lt {P i : Nat} (hP : 0 < P) : nextPhase P i < P :=
  Nat.mod_lt _ hP

theorem nextPhase_eq_ite {P i : Nat} (hi : i < P) :
    nextPhase P i = if i + 1 < P then i + 1 else 0 := by
  unfold nextPhase
  split
  · rename_i hlt
    exact Nat.mod_eq_of_lt hlt
  · rename_i hge
    have heq : i + 1 = P := by omega
    rw [heq, Nat.mod_self]

theorem prevPhase_lt {P i : Nat} (hi : i < P) : prevPhase P i < P := by
  unfold prevPhase
  split <;> omega

theorem nextPhase_prevPhase {P i : Nat} (hi : i < P) :
    nextPhase P (prevPhase P i) = i := by
  unfold prevPhase
  split
  · rename_i hz
    subst hz
    rw [nextPhase_eq_ite (by omega)]
    split <;> omega
  · rename_i hnz
    rw [nextPhase_eq_ite (by omega)]
    split <;> omega

theorem prevPhase_nextPhase {P i : Nat} (hi : i < P) :
    prevPhase P (nextPhase P i) = i := by
  rw [nextPhase_eq_ite hi]
  unfold prevPhase
  split <;> split <;> omega

/-! ## L07: Layer step and axis parity -/

theorem layer_move (p : Point) (d : Direction) :
    layer (move p d) = layer p + layerDelta d := by
  cases d <;> simp [layer, weight, move, layerDelta] <;> omega

theorem layerDelta_unit (d : Direction) :
    layerDelta d = 1 ∨ layerDelta d = -1 := by
  cases d <;> simp [layerDelta]

theorem layer_wordPos_succ (w : Nat → Bool) (i : Nat) :
    layer (wordPos w (i + 1)) = layer (wordPos w i) + layerDelta (outDir w i) := by
  change layer (move (wordPos w i) (outDir w i)) = _
  exact layer_move _ _

theorem layer_wordPos_nextPhase {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    layer (wordPos w (nextPhase P i)) = layer (wordPos w i) + layerDelta (outDir w i) := by
  rw [nextPhase_eq_ite hi]
  split
  · exact layer_wordPos_succ w i
  · rename_i hge
    have heq : i + 1 = P := by omega
    have hstep := layer_wordPos_succ w i
    rw [heq] at hstep
    have hP0 : layer (wordPos w P) = layer (wordPos w 0) := by
      change layer (wordDrift P w) = layer (wordPos w 0)
      rw [hd]
      simp [layer, weight, wordPos, wordTrace]
    omega

theorem layer_wordPos_nextPhase_pm {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    layer (wordPos w (nextPhase P i)) = layer (wordPos w i) + 1 ∨
      layer (wordPos w (nextPhase P i)) = layer (wordPos w i) - 1 := by
  rw [layer_wordPos_nextPhase hd hi]
  rcases layerDelta_unit (outDir w i) with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (by omega)

theorem inDir_nextPhase {P i : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hi : i < P) :
    inDir w (nextPhase P i) = outDir w i := by
  rw [nextPhase_eq_ite hi]
  split
  · rfl
  · rename_i hge
    have heq : i + 1 = P := by omega
    have hstep : (wordTrace w (i + 1)).2 = outDir w i := rfl
    rw [heq, hdir] at hstep
    simpa [inDir, wordTrace] using hstep

theorem outDir_prevPhase {P i : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hi : i < P) :
    outDir w (prevPhase P i) = inDir w i := by
  have h := inDir_nextPhase hdir (prevPhase_lt hi)
  rw [nextPhase_prevPhase hi] at h
  exact h.symm

theorem layer_wordPos_prevPhase {P i : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    layer (wordPos w i) = layer (wordPos w (prevPhase P i)) + layerDelta (inDir w i) := by
  have h := layer_wordPos_nextPhase hd (prevPhase_lt hi)
  rw [nextPhase_prevPhase hi, outDir_prevPhase hdir hi] at h
  exact h

theorem ContinuousPhasePath.layer_step {P len : Nat} {w : Nat → Bool}
    (p : ContinuousPhasePath P len) {r : Nat} (hr : r < len) :
    layer (p.pos w (r + 1)) = layer (p.pos w r) + layerDelta (outDir w (p.phase r)) := by
  rw [p.pos_step hr]
  exact layer_move _ _

theorem layer_wordPos_parity (w : Nat → Bool) (i : Nat) :
    (layer (wordPos w i) - (i : Int)) % 2 = 0 := by
  have h := linearForm_wordPos_parity (u := w) (s1 := 1) (s2 := 1) (Or.inl rfl) (Or.inl rfl) i
  simpa [layer, weight, linearForm] using h

/-- L07 axis parity in the word frame: horizontal arrival iff odd layer. -/
theorem inDir_horizontal_eq (w : Nat → Bool) (i : Nat) :
    (inDir w i).horizontal = decide (layer (wordPos w i) % 2 = 1) := by
  have ha : (inDir w i).horizontal = decide (i % 2 = 1) := wordTrace_axis w i
  have hp := layer_wordPos_parity w i
  rw [ha]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem inDir_horizontal_iff (w : Nat → Bool) (i : Nat) :
    (inDir w i).horizontal = true ↔ layer (wordPos w i) % 2 = 1 := by
  rw [inDir_horizontal_eq]
  simp

theorem same_layer_same_axis (w : Nat → Bool) {i j : Nat}
    (hl : layer (wordPos w i) = layer (wordPos w j)) :
    (inDir w i).horizontal = (inDir w j).horizontal := by
  rw [inDir_horizontal_eq, inDir_horizontal_eq, hl]

theorem alpha_iff_prev_above {P i : Nat} {w : Nat → Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    alpha w i = true ↔ layer (wordPos w (prevPhase P i)) = layer (wordPos w i) + 1 := by
  have hp := layer_wordPos_prevPhase hdir hd hi
  unfold alpha
  cases hd' : inDir w i <;> rw [hd'] at hp <;> simp [layerDelta] at hp ⊢ <;> omega

theorem beta_iff_next_above {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    beta w i = true ↔ layer (wordPos w (nextPhase P i)) = layer (wordPos w i) + 1 := by
  have hn := layer_wordPos_nextPhase hd hi
  unfold beta
  cases hd' : outDir w i <;> rw [hd'] at hn <;> simp [layerDelta] at hn ⊢ <;> omega

/-! ## Extremal layer bounds and L08 -/

theorem layer_le_topLayer {P i : Nat} {w : Nat → Bool} (hi : i < P) :
    layer (wordPos w i) ≤ topLayer P w := by
  apply mem_le_foldl_max
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem exists_topLayer_phase {P : Nat} {w : Nat → Bool} (hP : 0 < P) :
    ∃ i, i < P ∧ layer (wordPos w i) = topLayer P w := by
  rcases foldl_max_mem_or_init 0 ((List.range P).map (fun i => layer (wordPos w i))) with h0 | hmem
  · refine ⟨0, hP, ?_⟩
    change layer (wordPos w 0) = ((List.range P).map (fun i => layer (wordPos w i))).foldl max 0
    rw [h0]
    simp [layer, weight, wordPos, wordTrace]
  · obtain ⟨i, hi, hli⟩ := List.mem_map.mp hmem
    exact ⟨i, List.mem_range.mp hi, hli⟩

theorem botLayer_le_layer {P i : Nat} {w : Nat → Bool} (hi : i < P) :
    botLayer P w ≤ layer (wordPos w i) := by
  apply foldl_min_le_mem
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem exists_botLayer_phase {P : Nat} {w : Nat → Bool} (hP : 0 < P) :
    ∃ i, i < P ∧ layer (wordPos w i) = botLayer P w := by
  rcases foldl_min_mem_or_init 0 ((List.range P).map (fun i => layer (wordPos w i))) with h0 | hmem
  · refine ⟨0, hP, ?_⟩
    change layer (wordPos w 0) = ((List.range P).map (fun i => layer (wordPos w i))).foldl min 0
    rw [h0]
    simp [layer, weight, wordPos, wordTrace]
  · obtain ⟨i, hi, hli⟩ := List.mem_map.mp hmem
    exact ⟨i, List.mem_range.mp hi, hli⟩

theorem depth_nonneg {P i : Nat} {w : Nat → Bool} (hi : i < P) :
    0 ≤ depth P w i := by
  unfold depth
  have := layer_le_topLayer (w := w) hi
  omega

theorem botLayer_le_topLayer {P : Nat} {w : Nat → Bool} (hP : 0 < P) :
    botLayer P w ≤ topLayer P w := by
  have h1 := botLayer_le_layer (w := w) hP
  have h2 := layer_le_topLayer (w := w) hP
  omega

/-- Every visited layer contains a phase of `stableRank = 0`. -/
theorem exists_rank_zero_of_layer_nonempty {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int} (hne : layerPhases P w L ≠ []) :
    ∃ i, i < P ∧ layer (wordPos w i) = L ∧ stableRank P w i = 0 := by
  obtain ⟨i, hi_mem, hmin⟩ := exists_min_by (stableTime P w) (layerPhases P w L) hne
  obtain ⟨hi, hli⟩ := mem_layerPhases.mp hi_mem
  refine ⟨i, hi, hli, ?_⟩
  unfold stableRank
  have hnil : priorPhases P w i = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    obtain ⟨hjP, hjl, hjt⟩ := (mem_priorPhases_iff_stableTime hd hi).mp hj
    have hj_mem : j ∈ layerPhases P w L := mem_layerPhases.mpr ⟨hjP, hjl.trans hli⟩
    have := hmin j hj_mem
    omega
  simp [hnil]

/-- Any layer containing two distinct phases, one of rank `0`, also contains a phase of rank `1`. -/
theorem exists_rank_one_of_two_phases {P i j : Nat} {w : Nat → Bool} {L : Int}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hli : layer (wordPos w i) = L) (hlj : layer (wordPos w j) = L)
    (hr0 : stableRank P w i = 0) (hne : j ≠ i) :
    ∃ k, k < P ∧ layer (wordPos w k) = L ∧ stableRank P w k = 1 := by
  let above := (layerPhases P w L).filter (fun m => decide (stableTime P w i < stableTime P w m))
  have hj_lt : stableTime P w i < stableTime P w j := by
    have hj_not_prior : j ∉ priorPhases P w i := by
      have hnil : priorPhases P w i = [] := List.eq_nil_of_length_eq_zero hr0
      simp [hnil]
    rw [mem_priorPhases_iff_stableTime hd hi] at hj_not_prior
    have hneq : stableTime P w j ≠ stableTime P w i :=
      fun he => hne (stableTime_injective hj hi he)
    have hnotlt : ¬ stableTime P w j < stableTime P w i :=
      fun hlt => hj_not_prior ⟨hj, hlj.trans hli.symm, hlt⟩
    omega
  have hj_above : j ∈ above := by
    simp [above, mem_layerPhases, hj, hlj, hj_lt]
  obtain ⟨k, hk_above, hmin⟩ := exists_min_by (stableTime P w) above (List.ne_nil_of_mem hj_above)
  have hk_pair := List.mem_filter.mp hk_above
  obtain ⟨hk, hlk⟩ := mem_layerPhases.mp hk_pair.1
  have hik : stableTime P w i < stableTime P w k := by simpa using hk_pair.2
  refine ⟨k, hk, hlk, ?_⟩
  have hrk : stableRank P w k = stableRank P w i + 1 := by
    apply (stableRank_succ_iff hd hi hk (hli.trans hlk.symm)).mpr
    refine ⟨hik, ?_⟩
    rintro ⟨m, hm, hml, him, hmk⟩
    have hm_above : m ∈ above := by
      simp [above, mem_layerPhases, hm, hml.trans hli, him]
    have := hmin m hm_above
    omega
  omega

private theorem topLayer_forced_turn {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (htop : layer (wordPos w i) = topLayer P w) :
    w i = !(inDir w i).horizontal ∧ layerDelta (inDir w i) = 1 ∧ layerDelta (outDir w i) = -1 := by
  have hprev := layer_wordPos_prevPhase h.1 hd hi
  have hprev_le : layer (wordPos w (prevPhase P i)) ≤ topLayer P w :=
    layer_le_topLayer (prevPhase_lt hi)
  have hnext := layer_wordPos_nextPhase hd hi
  have hnext_le : layer (wordPos w (nextPhase P i)) ≤ topLayer P w :=
    layer_le_topLayer (nextPhase_lt h.period_pos)
  have hin : layerDelta (inDir w i) = 1 := by
    rcases layerDelta_unit (inDir w i) with h1 | h1 <;> omega
  have hout : layerDelta (outDir w i) = -1 := by
    rcases layerDelta_unit (outDir w i) with h1 | h1 <;> omega
  refine ⟨?_, hin, hout⟩
  unfold outDir at hout
  cases hd' : inDir w i <;> cases hw : w i <;>
    simp [hd', hw, turn, Direction.left, Direction.right, Direction.horizontal, layerDelta] at hin hout ⊢

private theorem botLayer_forced_turn {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (hbot : layer (wordPos w i) = botLayer P w) :
    w i = !(inDir w i).horizontal ∧ layerDelta (inDir w i) = -1 ∧ layerDelta (outDir w i) = 1 := by
  have hprev := layer_wordPos_prevPhase h.1 hd hi
  have hprev_ge : botLayer P w ≤ layer (wordPos w (prevPhase P i)) :=
    botLayer_le_layer (prevPhase_lt hi)
  have hnext := layer_wordPos_nextPhase hd hi
  have hnext_ge : botLayer P w ≤ layer (wordPos w (nextPhase P i)) :=
    botLayer_le_layer (nextPhase_lt h.period_pos)
  have hin : layerDelta (inDir w i) = -1 := by
    rcases layerDelta_unit (inDir w i) with h1 | h1 <;> omega
  have hout : layerDelta (outDir w i) = 1 := by
    rcases layerDelta_unit (outDir w i) with h1 | h1 <;> omega
  refine ⟨?_, hin, hout⟩
  unfold outDir at hout
  cases hd' : inDir w i <;> cases hw : w i <;>
    simp [hd', hw, turn, Direction.left, Direction.right, Direction.horizontal, layerDelta] at hin hout ⊢

/-- L08 (top): `topLayer` has a unique phase, of rank `0`, reading white, entering `.east` and leaving `.south`. -/
theorem topLayer_unique_phase {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    ∃ i, i < P ∧ layer (wordPos w i) = topLayer P w ∧
      (∀ j, j < P → layer (wordPos w j) = topLayer P w → j = i) ∧
      stableRank P w i = 0 ∧ w i = false ∧ inDir w i = .east ∧ outDir w i = .south := by
  obtain ⟨i0, hi0, htop0⟩ := exists_topLayer_phase (w := w) h.period_pos
  have hne : layerPhases P w (topLayer P w) ≠ [] :=
    List.ne_nil_of_mem (mem_layerPhases.mpr ⟨hi0, htop0⟩)
  obtain ⟨i, hi, htop, hr0⟩ := exists_rank_zero_of_layer_nonempty hd hne
  have hwi : w i = false := by
    rw [h.stableRank_color hi, hr0]
    rfl
  obtain ⟨hcol, hin, hout⟩ := topLayer_forced_turn h hd hi htop
  have hdir_in : inDir w i = .east := by
    cases hd' : inDir w i <;>
      simp [hd', hwi, Direction.horizontal, layerDelta] at hcol hin ⊢
  have hdir_out : outDir w i = .south := by
    simp [outDir, hwi, hdir_in, turn, Direction.right]
  have huniq : ∀ j, j < P → layer (wordPos w j) = topLayer P w → j = i := by
    intro j hj htopj
    by_cases hji : j = i
    · exact hji
    · exfalso
      obtain ⟨k, hk, htopk, hr1⟩ := exists_rank_one_of_two_phases hd hi hj htop htopj hr0 hji
      have hwk : w k = true := by
        rw [h.stableRank_color hk, hr1]
        rfl
      have hcolk := (topLayer_forced_turn h hd hk htopk).1
      have hax : (inDir w k).horizontal = (inDir w i).horizontal :=
        same_layer_same_axis w (htopk.trans htop.symm)
      rw [hax, hdir_in] at hcolk
      simp [Direction.horizontal, hwk] at hcolk
  exact ⟨i, hi, htop, huniq, hr0, hwi, hdir_in, hdir_out⟩

theorem topLayer_phase_eq {P i j : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hti : layer (wordPos w i) = topLayer P w) (htj : layer (wordPos w j) = topLayer P w) :
    i = j := by
  obtain ⟨t, _, _, huniq, _⟩ := topLayer_unique_phase h hd
  rw [huniq i hi hti, huniq j hj htj]

theorem topLayer_phase_props {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (htop : layer (wordPos w i) = topLayer P w) :
    stableRank P w i = 0 ∧ w i = false ∧ inDir w i = .east ∧ outDir w i = .south := by
  obtain ⟨t, _, _, huniq, hr0, hwt, hin, hout⟩ := topLayer_unique_phase h hd
  have heq : i = t := huniq i hi htop
  subst heq
  exact ⟨hr0, hwt, hin, hout⟩

theorem layerPhases_topLayer_eq {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (htop : layer (wordPos w i) = topLayer P w) :
    layerPhases P w (topLayer P w) = [i] :=
  list_eq_singleton_of_nodup (layerPhases_nodup P w (topLayer P w))
    (mem_layerPhases.mpr ⟨hi, htop⟩)
    (fun _ hj => let ⟨hjP, hlj⟩ := mem_layerPhases.mp hj; topLayer_phase_eq h hd hjP hi hlj htop)

theorem layerPhases_topLayer_length {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    (layerPhases P w (topLayer P w)).length = 1 := by
  obtain ⟨i, hi, htop, _⟩ := topLayer_unique_phase h hd
  rw [layerPhases_topLayer_eq h hd hi htop]
  rfl

/-- L08 (bottom): `botLayer` has a unique phase, of rank `0`, reading white, entering `.west` and leaving `.north`. -/
theorem botLayer_unique_phase {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    ∃ i, i < P ∧ layer (wordPos w i) = botLayer P w ∧
      (∀ j, j < P → layer (wordPos w j) = botLayer P w → j = i) ∧
      stableRank P w i = 0 ∧ w i = false ∧ inDir w i = .west ∧ outDir w i = .north := by
  obtain ⟨i0, hi0, hbot0⟩ := exists_botLayer_phase (w := w) h.period_pos
  have hne : layerPhases P w (botLayer P w) ≠ [] :=
    List.ne_nil_of_mem (mem_layerPhases.mpr ⟨hi0, hbot0⟩)
  obtain ⟨i, hi, hbot, hr0⟩ := exists_rank_zero_of_layer_nonempty hd hne
  have hwi : w i = false := by
    rw [h.stableRank_color hi, hr0]
    rfl
  obtain ⟨hcol, hin, hout⟩ := botLayer_forced_turn h hd hi hbot
  have hdir_in : inDir w i = .west := by
    cases hd' : inDir w i <;>
      simp [hd', hwi, Direction.horizontal, layerDelta] at hcol hin ⊢
  have hdir_out : outDir w i = .north := by
    simp [outDir, hwi, hdir_in, turn, Direction.right]
  have huniq : ∀ j, j < P → layer (wordPos w j) = botLayer P w → j = i := by
    intro j hj hbotj
    by_cases hji : j = i
    · exact hji
    · exfalso
      obtain ⟨k, hk, hbotk, hr1⟩ := exists_rank_one_of_two_phases hd hi hj hbot hbotj hr0 hji
      have hwk : w k = true := by
        rw [h.stableRank_color hk, hr1]
        rfl
      have hcolk := (botLayer_forced_turn h hd hk hbotk).1
      have hax : (inDir w k).horizontal = (inDir w i).horizontal :=
        same_layer_same_axis w (hbotk.trans hbot.symm)
      rw [hax, hdir_in] at hcolk
      simp [Direction.horizontal, hwk] at hcolk
  exact ⟨i, hi, hbot, huniq, hr0, hwi, hdir_in, hdir_out⟩

theorem botLayer_phase_eq {P i j : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hbi : layer (wordPos w i) = botLayer P w) (hbj : layer (wordPos w j) = botLayer P w) :
    i = j := by
  obtain ⟨b, _, _, huniq, _⟩ := botLayer_unique_phase h hd
  rw [huniq i hi hbi, huniq j hj hbj]

theorem botLayer_phase_props {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (hbot : layer (wordPos w i) = botLayer P w) :
    stableRank P w i = 0 ∧ w i = false ∧ inDir w i = .west ∧ outDir w i = .north := by
  obtain ⟨b, _, _, huniq, hr0, hwb, hin, hout⟩ := botLayer_unique_phase h hd
  have heq : i = b := huniq i hi hbot
  subst heq
  exact ⟨hr0, hwb, hin, hout⟩

theorem layerPhases_botLayer_eq {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (hbot : layer (wordPos w i) = botLayer P w) :
    layerPhases P w (botLayer P w) = [i] :=
  list_eq_singleton_of_nodup (layerPhases_nodup P w (botLayer P w))
    (mem_layerPhases.mpr ⟨hi, hbot⟩)
    (fun _ hj => let ⟨hjP, hlj⟩ := mem_layerPhases.mp hj; botLayer_phase_eq h hd hjP hi hlj hbot)

theorem layerPhases_botLayer_length {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    (layerPhases P w (botLayer P w)).length = 1 := by
  obtain ⟨i, hi, hbot, _⟩ := botLayer_unique_phase h hd
  rw [layerPhases_botLayer_eq h hd hi hbot]
  rfl

/-! ## L09: Top/bottom parity, width bounds, and discrete intermediate values -/

theorem topLayer_odd {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    topLayer P w % 2 = 1 := by
  obtain ⟨i, _, htop, _, _, _, hin, _⟩ := topLayer_unique_phase h hd
  have hax := (inDir_horizontal_iff w i).mp (by simp [hin, Direction.horizontal])
  rw [htop] at hax
  exact hax

theorem botLayer_odd {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    botLayer P w % 2 = 1 := by
  obtain ⟨i, _, hbot, _, _, _, hin, _⟩ := botLayer_unique_phase h hd
  have hax := (inDir_horizontal_iff w i).mp (by simp [hin, Direction.horizontal])
  rw [hbot] at hax
  exact hax

theorem layerWidth_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    layerWidth P w % 2 = 0 := by
  have ht := topLayer_odd h hd
  have hb := botLayer_odd h hd
  unfold layerWidth
  omega

theorem layerWidth_ge_two {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    2 ≤ layerWidth P w := by
  obtain ⟨i, hi, htop, _, _, _, _, hout⟩ := topLayer_unique_phase h hd
  have hnext := layer_wordPos_nextPhase hd hi
  rw [htop, hout] at hnext
  have hbot_le : botLayer P w ≤ layer (wordPos w (nextPhase P i)) :=
    botLayer_le_layer (nextPhase_lt h.period_pos)
  have ht := topLayer_odd h hd
  have hb := botLayer_odd h hd
  simp only [layerDelta] at hnext
  unfold layerWidth
  omega

theorem layerWidth_pos {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    0 < layerWidth P w := by
  have := layerWidth_ge_two h hd
  omega

/-- L09 discrete intermediate values: every layer between `botLayer` and `topLayer` is visited. -/
theorem exists_phase_of_layer_between {P : Nat} {w : Nat → Bool}
    (hP : 0 < P) {L : Int} (hlo : botLayer P w ≤ L) (hhi : L ≤ topLayer P w) :
    ∃ i, i < P ∧ layer (wordPos w i) = L := by
  obtain ⟨iBot, hiBot, hbot⟩ := exists_botLayer_phase (w := w) hP
  obtain ⟨iTop, hiTop, htop⟩ := exists_topLayer_phase (w := w) hP
  have hstep : ∀ k, layer (wordPos w (k + 1)) = layer (wordPos w k) + 1 ∨
      layer (wordPos w (k + 1)) = layer (wordPos w k) - 1 := by
    intro k
    rw [layer_wordPos_succ]
    rcases layerDelta_unit (outDir w k) with h1 | h1 <;> rw [h1]
    · exact Or.inl rfl
    · exact Or.inr (by omega)
  by_cases hle : iBot ≤ iTop
  · have hrange : layer (wordPos w iBot) ≤ L ∧ L ≤ layer (wordPos w (iBot + (iTop - iBot))) := by
      rw [show iBot + (iTop - iBot) = iTop by omega, hbot, htop]
      exact ⟨hlo, hhi⟩
    obtain ⟨k, _, hk_le, hfk⟩ :=
      discrete_ivt (fun n => layer (wordPos w n)) hstep iBot (iTop - iBot) L (Or.inl hrange)
    exact ⟨k, by omega, hfk⟩
  · have hrange : layer (wordPos w (iTop + (iBot - iTop))) ≤ L ∧ L ≤ layer (wordPos w iTop) := by
      rw [show iTop + (iBot - iTop) = iBot by omega, hbot, htop]
      exact ⟨hlo, hhi⟩
    obtain ⟨k, _, hk_le, hfk⟩ :=
      discrete_ivt (fun n => layer (wordPos w n)) hstep iTop (iBot - iTop) L (Or.inr hrange)
    exact ⟨k, by omega, hfk⟩

theorem layerPhases_ne_nil_of_between {P : Nat} {w : Nat → Bool}
    (hP : 0 < P) {L : Int} (hlo : botLayer P w ≤ L) (hhi : L ≤ topLayer P w) :
    layerPhases P w L ≠ [] := by
  obtain ⟨i, hi, hli⟩ := exists_phase_of_layer_between (w := w) hP hlo hhi
  exact List.ne_nil_of_mem (mem_layerPhases.mpr ⟨hi, hli⟩)

/-! ## L14: Port XOR identity and heading determination from depth parity -/

theorem depth_even_iff_layer_odd {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (i : Nat) :
    depth P w i % 2 = 0 ↔ layer (wordPos w i) % 2 = 1 := by
  have ht := topLayer_odd h hd
  unfold depth
  omega

theorem depth_odd_iff_layer_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (i : Nat) :
    depth P w i % 2 = 1 ↔ layer (wordPos w i) % 2 = 0 := by
  have ht := topLayer_odd h hd
  unfold depth
  omega

theorem inDir_horizontal_eq_depth_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (i : Nat) :
    (inDir w i).horizontal = decide (depth P w i % 2 = 0) := by
  rw [inDir_horizontal_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (depth_even_iff_layer_odd h hd i).symm

theorem depth_odd_decide_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (i : Nat) :
    decide (depth P w i % 2 = 1) = !(inDir w i).horizontal := by
  rw [inDir_horizontal_eq_depth_even h hd i]
  by_cases he : depth P w i % 2 = 0
  · simp [he]
  · have ho : depth P w i % 2 = 1 := by omega
    simp [ho]

/-- L14 (`inDir` table): arrival heading is uniquely determined by `(depth parity, alpha)`. -/
theorem inDir_eq_of_depth_alpha {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (i : Nat) :
    inDir w i =
      if depth P w i % 2 = 0 then
        if alpha w i then .west else .east
      else
        if alpha w i then .south else .north := by
  have hhor := inDir_horizontal_eq_depth_even h hd i
  unfold alpha
  cases hd' : inDir w i <;> rw [hd'] at hhor <;>
    simp [Direction.horizontal] at hhor ⊢ <;> simp [hhor]

theorem inDir_of_depth_even_alpha_true {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 0) (ha : alpha w i = true) : inDir w i = .west := by
  simp [inDir_eq_of_depth_alpha h hd i, hdep, ha]

theorem inDir_of_depth_even_alpha_false {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 0) (ha : alpha w i = false) : inDir w i = .east := by
  simp [inDir_eq_of_depth_alpha h hd i, hdep, ha]

theorem inDir_of_depth_odd_alpha_true {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 1) (ha : alpha w i = true) : inDir w i = .south := by
  have hne : depth P w i % 2 ≠ 0 := by omega
  simp [inDir_eq_of_depth_alpha h hd i, hne, ha]

theorem inDir_of_depth_odd_alpha_false {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 1) (ha : alpha w i = false) : inDir w i = .north := by
  have hne : depth P w i % 2 ≠ 0 := by omega
  simp [inDir_eq_of_depth_alpha h hd i, hne, ha]

/-- L14 (`outDir` table): departure heading is uniquely determined by `(depth parity, beta)`. -/
theorem outDir_eq_of_depth_beta {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (i : Nat) :
    outDir w i =
      if depth P w i % 2 = 0 then
        if beta w i then .north else .south
      else
        if beta w i then .east else .west := by
  have hhor := inDir_horizontal_eq_depth_even h hd i
  unfold beta outDir
  cases hd' : inDir w i <;> rw [hd'] at hhor <;> cases w i <;>
    simp [Direction.horizontal, turn, Direction.left, Direction.right] at hhor ⊢ <;>
    simp [hhor]

theorem outDir_of_depth_even_beta_true {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 0) (hb : beta w i = true) : outDir w i = .north := by
  simp [outDir_eq_of_depth_beta h hd i, hdep, hb]

theorem outDir_of_depth_even_beta_false {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 0) (hb : beta w i = false) : outDir w i = .south := by
  simp [outDir_eq_of_depth_beta h hd i, hdep, hb]

theorem outDir_of_depth_odd_beta_true {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 1) (hb : beta w i = true) : outDir w i = .east := by
  have hne : depth P w i % 2 ≠ 0 := by omega
  simp [outDir_eq_of_depth_beta h hd i, hne, hb]

theorem outDir_of_depth_odd_beta_false {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hdep : depth P w i % 2 = 1) (hb : beta w i = false) : outDir w i = .west := by
  have hne : depth P w i % 2 ≠ 0 := by omega
  simp [outDir_eq_of_depth_beta h hd i, hne, hb]

/-- L14 (port XOR identity): for every phase `i < P`,
`beta w i = xor (xor (alpha w i) (decide (stableRank P w i % 2 = 1))) (decide (depth P w i % 2 = 1))`. -/
theorem beta_eq_xor {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    beta w i =
      xor (xor (alpha w i) (decide (stableRank P w i % 2 = 1)))
        (decide (depth P w i % 2 = 1)) := by
  rw [← h.stableRank_color hi, depth_odd_decide_eq h hd i]
  unfold beta outDir alpha
  cases inDir w i <;> cases w i <;> rfl

theorem topLayer_ports {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (htop : layer (wordPos w i) = topLayer P w) :
    alpha w i = false ∧ beta w i = false := by
  obtain ⟨_, _, hin, hout⟩ := topLayer_phase_props h hd hi htop
  simp [alpha, beta, hin, hout]

theorem botLayer_ports {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (hi : i < P)
    (hbot : layer (wordPos w i) = botLayer P w) :
    alpha w i = true ∧ beta w i = true := by
  obtain ⟨_, _, hin, hout⟩ := botLayer_phase_props h hd hi hbot
  simp [alpha, beta, hin, hout]

end LangtonsAnt
