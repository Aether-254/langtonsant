import UnitDiagonalInterleave
import UnitDiagonalWords
import UnitDiagonalMatching
import UnitDiagonalExtremal
import UnitDiagonalReduction

/-!
Integration of the phase-level and list-level unit-diagonal interfaces.
All layers use the original word frame and depths relative to `topLayer`.
The exclusion theorem is not asserted until all continuous-path obligations close.
-/
namespace UnitDiagonal
open LangtonsAnt

@[simp] theorem matching_inDir (w : Nat → Bool) (i : Nat) :
    UnitDiagonalMatching.inDir w i = LangtonsAnt.inDir w i := rfl

@[simp] theorem matching_outDir (w : Nat → Bool) (i : Nat) :
    UnitDiagonalMatching.outDir w i = LangtonsAnt.outDir w i := rfl

/-- The unique phase with a specified stable rank on a layer. -/
noncomputable def phaseAtRank {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int)
    (r : Fin (layerPhases P w L).length) : Nat :=
  Classical.choose (stableRank_surjective_on_layer hd r.isLt)

theorem phaseAtRank_mem {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int)
    (r : Fin (layerPhases P w L).length) :
    phaseAtRank hd L r ∈ layerPhases P w L :=
  (Classical.choose_spec (stableRank_surjective_on_layer hd r.isLt)).1

@[simp] theorem phaseAtRank_rank {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int)
    (r : Fin (layerPhases P w L).length) :
    stableRank P w (phaseAtRank hd L r) = r.val :=
  (Classical.choose_spec (stableRank_surjective_on_layer hd r.isLt)).2

theorem phaseAtRank_eq {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int}
    (hi : i ∈ layerPhases P w L) :
    phaseAtRank hd L ⟨stableRank P w i, stableRank_lt_layer_length hd hi⟩ = i :=
  stableRank_injective_on_layer hd (phaseAtRank_mem hd L _) hi (phaseAtRank_rank hd L _)

/-- A layer's phases, enumerated by increasing stable rank. -/
noncomputable def rankedPhases {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) : List Nat :=
  List.ofFn (phaseAtRank hd L)

/-- A phase observable sampled in stable-rank order. -/
noncomputable def portWord {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) (f : Nat → Bool) : List Bool :=
  (rankedPhases hd L).map f

noncomputable def alphaWord {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) : List Bool :=
  portWord hd L (LangtonsAnt.alpha w)

noncomputable def betaWord {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) : List Bool :=
  portWord hd L (LangtonsAnt.beta w)

@[simp] theorem rankedPhases_length {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) :
    (rankedPhases hd L).length = (layerPhases P w L).length := by
  simp [rankedPhases]

@[simp] theorem portWord_length {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) (f : Nat → Bool) :
    (portWord hd L f).length = (layerPhases P w L).length := by
  simp [portWord]

theorem rankedPhases_perm {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) :
    (rankedPhases hd L).Perm (layerPhases P w L) := by
  have hn : (rankedPhases hd L).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj hij
    have := congrArg (stableRank P w) hij
    simpa only [rankedPhases, List.getElem_ofFn, phaseAtRank_rank] using this
  apply (List.perm_ext_iff_of_nodup hn (LangtonsAnt.layerPhases_nodup P w L)).mpr
  intro i
  simp only [rankedPhases, List.mem_ofFn]
  constructor
  · rintro ⟨r, rfl⟩
    exact phaseAtRank_mem hd L r
  · intro hi
    exact ⟨⟨stableRank P w i, stableRank_lt_layer_length hd hi⟩, phaseAtRank_eq hd hi⟩

theorem portWord_get {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) (f : Nat → Bool)
    (r : Fin (layerPhases P w L).length) :
    (portWord hd L f)[r.val]? = some (f (phaseAtRank hd L r)) := by
  simp [portWord, rankedPhases]

/-- The phase port formula is exactly the list port formula, with depth parity. -/
theorem betaWord_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (L : Int) :
    betaWord hd L = beta (alphaWord hd L) (decide ((topLayer P w - L) % 2 = 1)) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < (layerPhases P w L).length
  · let r : Fin (layerPhases P w L).length := ⟨k, hk⟩
    have hm := mem_layerPhases.mp (phaseAtRank_mem hd L r)
    rw [beta_spec]
    change (portWord hd L (LangtonsAnt.beta w))[k]? =
      ((portWord hd L (LangtonsAnt.alpha w))[k]?).map _
    rw [portWord_get hd L _ r, portWord_get hd L _ r]
    simp only [Option.map_some]
    rw [beta_eq_xor h hd hm.1, phaseAtRank_rank]
    simp only [depth, hm.2]
    rfl
  · have ha : (alphaWord hd L).length ≤ k := by simp [alphaWord]; omega
    have hb : (betaWord hd L).length ≤ k := by simp [betaWord]; omega
    rw [List.getElem?_eq_none hb, List.getElem?_eq_none (by rw [beta_length]; exact ha)]

private theorem countTrue_map (xs : List Nat) (f : Nat → Bool) :
    countTrue (xs.map f) = (xs.filter f).length := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases hf : f i <;> simp [countTrue, hf, ih] <;> omega

theorem portWord_count {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) (f : Nat → Bool) :
    countTrue (portWord hd L f) = ((layerPhases P w L).filter f).length := by
  rw [portWord, countTrue_map]
  exact ((rankedPhases_perm hd L).filter f).length_eq

private theorem cyclic_filter_count {P : Nat} (hP : 0 < P) (f g : Nat → Bool)
    (he : ∀ i, i < P → g (UnitDiagonalMatching.succ P i) = f i) :
    ((List.range P).filter f).length = ((List.range P).filter g).length := by
  have hh := ordered_bijection_position (List.range P) (List.range P)
    (UnitDiagonalMatching.succ P) (fun i _ => f i = true) (fun i _ => g i = true)
    List.nodup_range List.nodup_range
    (fun _ hi _ hj => UnitDiagonalMatching.succ_injective
      (List.mem_range.mp hi) (List.mem_range.mp hj))
    (fun j => by
      constructor
      · intro hj
        exact ⟨UnitDiagonalMatching.pred P j,
          List.mem_range.mpr (UnitDiagonalMatching.pred_lt (List.mem_range.mp hj)),
          UnitDiagonalMatching.succ_pred (List.mem_range.mp hj)⟩
      · rintro ⟨i, _, rfl⟩
        exact List.mem_range.mpr (UnitDiagonalMatching.succ_lt hP))
    (fun i hi _ _ => by rw [he i (List.mem_range.mp hi)])
    (List.mem_range.mpr hP)
  simpa only [Bool.decide_eq_true] using hh

private theorem filter_complement (xs : List Nat) (f : Nat → Bool) :
    (xs.filter (fun i => !f i)).length + (xs.filter f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases hf : f i <;> simp [hf] <;> omega

/-- L16: down departures at `L` are the from-above arrivals at `L - 1`.
The subtraction-free form also works for empty layers. -/
theorem cut_down_count {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (L : Int) :
    countTrue (alphaWord hd (L - 1)) + countTrue (betaWord hd L) =
      (layerPhases P w L).length := by
  have he := cyclic_filter_count h.period_pos
    (fun i => decide (layer (wordPos w i) = L) && !LangtonsAnt.beta w i)
    (fun i => decide (layer (wordPos w i) = L - 1) && LangtonsAnt.alpha w i) (by
      intro i hi
      have hs := UnitDiagonalMatching.successor_layer hd hi
      have hh := UnitDiagonalMatching.successor_heading h.1 hi
      simp only [matching_inDir, matching_outDir] at hs hh
      simp only [LangtonsAnt.alpha, hs, hh, LangtonsAnt.beta]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      cases outDir w i <;> simp [UnitDiagonalMatching.layerStep] <;> omega)
  have he' : ((layerPhases P w L).filter (fun i => !LangtonsAnt.beta w i)).length =
      ((layerPhases P w (L - 1)).filter (LangtonsAnt.alpha w)).length := by
    simpa only [layerPhases, List.filter_filter, Bool.and_comm] using he
  simp only [alphaWord, betaWord, portWord_count]
  rw [← he']
  exact filter_complement _ _

/-- L16: up departures at `L - 1` are the from-below arrivals at `L`. -/
theorem cut_up_count {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (L : Int) :
    countTrue (betaWord hd (L - 1)) + countTrue (alphaWord hd L) =
      (layerPhases P w L).length := by
  have he := cyclic_filter_count h.period_pos
    (fun i => decide (layer (wordPos w i) = L - 1) && LangtonsAnt.beta w i)
    (fun i => decide (layer (wordPos w i) = L) && !LangtonsAnt.alpha w i) (by
      intro i hi
      have hs := UnitDiagonalMatching.successor_layer hd hi
      have hh := UnitDiagonalMatching.successor_heading h.1 hi
      simp only [matching_inDir, matching_outDir] at hs hh
      simp only [LangtonsAnt.alpha, hs, hh, LangtonsAnt.beta]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      cases outDir w i <;> simp [UnitDiagonalMatching.layerStep] <;> omega)
  have he' : ((layerPhases P w (L - 1)).filter (LangtonsAnt.beta w)).length =
      ((layerPhases P w L).filter (fun i => !LangtonsAnt.alpha w i)).length := by
    simpa only [layerPhases, List.filter_filter, Bool.and_comm] using he
  simp only [alphaWord, betaWord, portWord_count]
  rw [he']
  exact filter_complement _ _

theorem top_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    countTrue (alphaWord hd (topLayer P w)) = 0 ∧
      countTrue (betaWord hd (topLayer P w)) = 0 := by
  obtain ⟨i, hi, hl, _⟩ := topLayer_unique_phase h hd
  have hp := topLayer_ports h hd hi hl
  simp [alphaWord, betaWord, portWord_count, layerPhases_topLayer_eq h hd hi hl,
    hp.1, hp.2]

/-- L16: every layer a natural depth below the top has equal port counts. -/
theorem depth_counts_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (n : Nat) :
    countTrue (alphaWord hd (topLayer P w - n)) =
      countTrue (betaWord hd (topLayer P w - n)) := by
  induction n with
  | zero => simpa using (top_counts h hd).1.trans (top_counts h hd).2.symm
  | succ n ih =>
    have hdown := cut_down_count h hd (topLayer P w - n)
    have hup := cut_up_count h hd (topLayer P w - n)
    have he : topLayer P w - ((n + 1 : Nat) : Int) = topLayer P w - n - 1 := by omega
    rw [he]
    omega

theorem layer_counts_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    {L : Int} (hL : L ≤ topLayer P w) :
    countTrue (alphaWord hd L) = countTrue (betaWord hd L) := by
  have he : topLayer P w - ((topLayer P w - L).toNat : Int) = L := by omega
  simpa only [he] using depth_counts_eq h hd (topLayer P w - L).toNat

theorem first_inner_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    countTrue (alphaWord hd (topLayer P w - 1)) = 1 ∧
      countTrue (betaWord hd (topLayer P w - 1)) = 1 := by
  have hdown := cut_down_count h hd (topLayer P w)
  have hup := cut_up_count h hd (topLayer P w)
  rw [(top_counts h hd).2, layerPhases_topLayer_length h hd] at hdown
  rw [(top_counts h hd).1, layerPhases_topLayer_length h hd] at hup
  exact ⟨by omega, by omega⟩

/-- L18 applied to actual phases: the first inner layer has one of four words. -/
theorem first_inner_four_words {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    let A := alphaWord hd (topLayer P w - 1)
    A = [true, false, false] ∨ A = [true, false, false, false] ∨
      A = [false, false, true] ∨ A = [false, false, true, false] := by
  have hc := first_inner_counts h hd
  have hb := betaWord_eq h hd (topLayer P w - 1)
  have he : topLayer P w - (topLayer P w - 1) = 1 := by omega
  simp only [he] at hb
  change betaWord hd (topLayer P w - 1) = beta (alphaWord hd (topLayer P w - 1)) true at hb
  apply odd_layer_single_true _ hc.1
  · rw [← hb]; exact hc.2
  · intro heq
    rw [heq] at hc
    simp [countTrue] at hc

theorem bottom_counts {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    countTrue (alphaWord hd (botLayer P w)) = 1 ∧
      countTrue (betaWord hd (botLayer P w)) = 1 := by
  obtain ⟨i, hi, hl, _⟩ := botLayer_unique_phase h hd
  have hp := botLayer_ports h hd hi hl
  simp [alphaWord, betaWord, portWord_count, layerPhases_botLayer_eq h hd hi hl,
    hp.1, hp.2]

/-- L17: a consistent unit-diagonal word would have width at least four. -/
theorem layerWidth_ge_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    4 ≤ layerWidth P w := by
  have htwo := layerWidth_ge_two h hd
  have heven := layerWidth_even h hd
  by_cases hnot : 4 ≤ layerWidth P w
  · exact hnot
  apply False.elim
  have hw : layerWidth P w = 2 := by omega
  have he : topLayer P w - 1 - 1 = botLayer P w := by unfold layerWidth at hw; omega
  have hc := cut_down_count h hd (topLayer P w - 1)
  rw [he, (bottom_counts h hd).1, (first_inner_counts h hd).2] at hc
  have hn : (alphaWord hd (topLayer P w - 1)).length = 2 := by
    simp only [alphaWord, portWord_length]
    omega
  have hf := first_inner_four_words h hd
  rcases hf with hf | hf | hf | hf <;> rw [hf] at hn <;> contradiction

theorem portWord_at_phase {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int} (hi : i ∈ layerPhases P w L)
    (f : Nat → Bool) :
    (portWord hd L f)[stableRank P w i]? = some (f i) := by
  have hh := portWord_get hd L f ⟨stableRank P w i, stableRank_lt_layer_length hd hi⟩
  rwa [phaseAtRank_eq hd hi] at hh

theorem alphaWord_at_phase {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int} (hi : i ∈ layerPhases P w L) :
    (alphaWord hd L)[stableRank P w i]? = some (LangtonsAnt.alpha w i) :=
  portWord_at_phase hd hi _

theorem betaWord_at_phase {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int} (hi : i ∈ layerPhases P w L) :
    (betaWord hd L)[stableRank P w i]? = some (LangtonsAnt.beta w i) :=
  portWord_at_phase hd hi _

/-- L19's obstruction: the unique incoming upper port on A cannot have rank two.
The two actual successor edges have displacement `(1,-1)` and time shift `2-P`. -/
theorem first_inner_not_late {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hA : alphaWord hd (topLayer P w - 1) = [false, false, true] ∨
      alphaWord hd (topLayer P w - 1) = [false, false, true, false]) : False := by
  let L := topLayer P w - 1
  have hlen : 3 ≤ (layerPhases P w L).length := by
    have hl := portWord_length hd L (LangtonsAnt.alpha w)
    change (alphaWord hd (topLayer P w - 1)).length = _ at hl
    rcases hA with ha | ha <;> rw [ha] at hl <;> simp at hl <;> omega
  let a := phaseAtRank hd L ⟨0, by omega⟩
  have ham := phaseAtRank_mem hd L ⟨0, by omega⟩
  change a ∈ layerPhases P w L at ham
  obtain ⟨haP, haL⟩ := mem_layerPhases.mp ham
  have har : stableRank P w a = 0 := phaseAtRank_rank hd L _
  have had : depth P w a = 1 := by unfold depth; dsimp [L] at haL; omega
  have hab : LangtonsAnt.beta w a = true := by
    have hb := betaWord_at_phase hd ham
    rw [betaWord_eq h hd L, har] at hb
    have he : topLayer P w - L = 1 := by dsimp [L]; omega
    rw [he] at hb
    rcases hA with ha | ha <;> change alphaWord hd L = _ at ha <;>
      rw [ha] at hb <;> exact Option.some.inj hb.symm
  have hao : outDir w a = .east :=
    outDir_of_depth_odd_beta_true h hd (by rw [had]; decide) hab
  let t := UnitDiagonalMatching.succ P a
  have htP : t < P := UnitDiagonalMatching.succ_lt h.period_pos
  have htL : layer (wordPos w t) = topLayer P w := by
    have hs := UnitDiagonalMatching.successor_layer hd haP
    simp only [matching_outDir, hao, UnitDiagonalMatching.layerStep, haL] at hs
    dsimp [t, L] at *
    omega
  have hto : outDir w t = .south := (topLayer_phase_props h hd htP htL).2.2.2
  let b := UnitDiagonalMatching.succ P t
  have hbP : b < P := UnitDiagonalMatching.succ_lt h.period_pos
  have hbL : layer (wordPos w b) = L := by
    have hs := UnitDiagonalMatching.successor_layer hd htP
    simpa only [matching_outDir, hto, UnitDiagonalMatching.layerStep, htL,
      Int.add_neg_one] using hs
  have hba : LangtonsAnt.alpha w b = true := by
    have hs := UnitDiagonalMatching.successor_heading h.1 htP
    simp only [matching_inDir, matching_outDir, hto] at hs
    simp [LangtonsAnt.alpha, show inDir w b = .south from hs]
  have hbr : stableRank P w b = 2 := by
    have hh := alphaWord_at_phase hd (mem_layerPhases.mpr ⟨hbP, hbL⟩)
    rw [hba] at hh
    have hm := mem_trueIdx.mpr hh
    rcases hA with ha | ha <;> change alphaWord hd L = _ at ha <;>
      rw [ha] at hm <;> simpa [trueIdx] using hm
  have htime := (stableRank_lt_iff_stableTime_lt hd haP hbP (haL.trans hbL.symm)).mp
    (by rw [har, hbr]; decide)
  have ht := UnitDiagonalMatching.successor_stableTime hd haP
  have hb := UnitDiagonalMatching.successor_stableTime hd htP
  simp only [matching_outDir, hao, hto, UnitDiagonalMatching.delta, Int.mul_one,
    Int.mul_zero, Int.sub_zero] at ht hb
  change stableTime P w t = _ at ht
  change stableTime P w b = _ at hb
  have hle : (layerPhases P w L).length ≤ P := by
    simpa only [layerPhases, List.length_range] using
      List.length_filter_le (fun i => decide (layer (wordPos w i) = L)) (List.range P)
  omega

/-- L19: the first inner word begins with its unique upper arrival. -/
theorem first_inner_two_words {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    alphaWord hd (topLayer P w - 1) = [true, false, false] ∨
      alphaWord hd (topLayer P w - 1) = [true, false, false, false] := by
  rcases first_inner_four_words h hd with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr ha
  · exact False.elim (first_inner_not_late h hd (Or.inl ha))
  · exact False.elim (first_inner_not_late h hd (Or.inr ha))

private theorem trueIdx_nodup (xs : List Bool) : (trueIdx xs).Nodup :=
  (pairwise_trueIdx xs).imp (fun h => Nat.ne_of_lt h)

/-- Counting earlier selected phases is counting earlier selected ranks. -/
theorem port_position {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int} (hi : i ∈ layerPhases P w L)
    (f : Nat → Bool) (hf : f i = true) :
    (((layerPhases P w L).filter f).filter
      (fun j => decide (stableRank P w j < stableRank P w i))).length =
    ((trueIdx (portWord hd L f)).filter (fun r => decide (r < stableRank P w i))).length := by
  apply ordered_bijection_position _ _ (stableRank P w)
    (fun j k => stableRank P w j < stableRank P w k) (· < ·)
    ((LangtonsAnt.layerPhases_nodup P w L).filter f) (trueIdx_nodup _)
    (fun _ hj _ hk => stableRank_injective_on_layer hd
      (List.mem_filter.mp hj).1 (List.mem_filter.mp hk).1) _
    (fun _ _ _ _ => Iff.rfl) (List.mem_filter.mpr ⟨hi, hf⟩)
  intro r
  constructor
  · intro hr
    have hv := mem_trueIdx.mp hr
    have hrlt : r < (layerPhases P w L).length := by
      simpa only [portWord_length] using lt_length_of_getElem? hv
    let j := phaseAtRank hd L ⟨r, hrlt⟩
    have hj := phaseAtRank_mem hd L ⟨r, hrlt⟩
    have hf' := portWord_get hd L f ⟨r, hrlt⟩
    rw [hv] at hf'
    exact ⟨j, List.mem_filter.mpr ⟨hj, (Option.some.inj hf').symm⟩,
      phaseAtRank_rank hd L _⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hjm, hjf⟩ := List.mem_filter.mp hj
    apply mem_trueIdx.mpr
    rw [portWord_at_phase hd hjm f, hjf]

private theorem sorted_get_position {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {k a : Nat} (hk : xs[k]? = some a) :
    (xs.filter (fun r => decide (r < a))).length = k := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons b xs ih =>
    obtain ⟨hb, ht⟩ := List.pairwise_cons.mp hs
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst a
      have hn : xs.filter (fun r => decide (r < b)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro r hr
        have := hb r hr
        simp only [decide_eq_true_eq]
        omega
      simp [hn]
    | succ k =>
      have hak : xs[k]? = some a := hk
      have hba := hb a (List.mem_iff_getElem?.mpr ⟨k, hak⟩)
      simpa [hba] using ih ht hak

private theorem sorted_get_at_position {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {a : Nat} (ha : a ∈ xs) :
    xs[(xs.filter (fun r => decide (r < a))).length]? = some a := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
  rw [sorted_get_position hs hk]
  exact hk

/-- L12 in a lookup-ready form: a directed successor preserves its port-list index. -/
theorem successor_port_index {P i k : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) {L : Int} {d : Direction}
    (hi : i ∈ UnitDiagonalMatching.departures P w L d)
    (hk : (trueIdx (portWord hd L (fun j => decide (outDir w j = d))))[k]? =
      some (stableRank P w i)) :
    (trueIdx (portWord hd (L + UnitDiagonalMatching.layerStep d)
      (fun j => decide (inDir w j = d))))[k]? =
      some (stableRank P w (UnitDiagonalMatching.succ P i)) := by
  have hj := (UnitDiagonalMatching.successor_mem_iff h.1 hd
    (UnitDiagonalMatching.mem_departures.mp hi).1).mpr hi
  obtain ⟨hiP, hiL, hid⟩ := UnitDiagonalMatching.mem_departures.mp hi
  obtain ⟨hjP, hjL, hjd⟩ := UnitDiagonalMatching.mem_arrivals.mp hj
  have hm := UnitDiagonalMatching.departure_rank_position_eq_arrival_rank_position h.1 hd hi
  change (((layerPhases P w L).filter (fun j => decide (outDir w j = d))).filter _).length =
    (((layerPhases P w (L + UnitDiagonalMatching.layerStep d)).filter
      (fun j => decide (inDir w j = d))).filter _).length at hm
  rw [port_position hd (mem_layerPhases.mpr ⟨hiP, hiL⟩) _ (by simpa using hid),
    port_position hd (mem_layerPhases.mpr ⟨hjP, hjL⟩) _ (by simpa using hjd),
    sorted_get_position (pairwise_trueIdx _) hk] at hm
  rw [hm]
  apply sorted_get_at_position (pairwise_trueIdx _)
  apply mem_trueIdx.mpr
  rw [portWord_at_phase hd (mem_layerPhases.mpr ⟨hjP, hjL⟩)]
  simpa using hjd

theorem portWord_congr {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) {L : Int} {f g : Nat → Bool}
    (he : ∀ i ∈ layerPhases P w L, f i = g i) :
    portWord hd L f = portWord hd L g := by
  apply List.map_congr_left
  intro i hi
  exact he i ((rankedPhases_perm hd L).mem_iff.mp hi)

theorem portWord_not {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (L : Int) (f : Nat → Bool) :
    portWord hd L (fun i => !f i) = (portWord hd L f).map (!·) := by
  simp [portWord, List.map_map, Function.comp_def]

def enterDir (n : Nat) (b : Bool) : Direction :=
  if n % 2 = 0 then (if b then .west else .east) else (if b then .south else .north)

def leaveDir (n : Nat) (b : Bool) : Direction :=
  if n % 2 = 0 then (if b then .north else .south) else (if b then .east else .west)

theorem incoming_portWord {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (n : Nat) (b : Bool) :
    portWord hd (topLayer P w - n) (fun i => decide (inDir w i = enterDir n b)) =
      if b then alphaWord hd (topLayer P w - n)
      else (alphaWord hd (topLayer P w - n)).map (!·) := by
  have he (i : Nat) (hi : i ∈ layerPhases P w (topLayer P w - n)) :
      decide (inDir w i = enterDir n b) =
        if b then LangtonsAnt.alpha w i else !LangtonsAnt.alpha w i := by
    have hl := (mem_layerPhases.mp hi).2
    have hd' : depth P w i = n := by unfold depth; omega
    have hp : (n : Int) % 2 = 0 ↔ n % 2 = 0 := by omega
    rw [inDir_eq_of_depth_alpha h hd i, hd']
    simp only [hp]
    cases b <;> cases LangtonsAnt.alpha w i <;>
      by_cases hn : n % 2 = 0 <;> simp [enterDir, hn]
  cases b
  · simp only [Bool.false_eq_true, ite_false, alphaWord]
    rw [← portWord_not]
    exact portWord_congr hd he
  · exact portWord_congr hd he

theorem outgoing_portWord {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) (n : Nat) (b : Bool) :
    portWord hd (topLayer P w - n) (fun i => decide (outDir w i = leaveDir n b)) =
      if b then betaWord hd (topLayer P w - n)
      else (betaWord hd (topLayer P w - n)).map (!·) := by
  have he (i : Nat) (hi : i ∈ layerPhases P w (topLayer P w - n)) :
      decide (outDir w i = leaveDir n b) =
        if b then LangtonsAnt.beta w i else !LangtonsAnt.beta w i := by
    have hl := (mem_layerPhases.mp hi).2
    have hd' : depth P w i = n := by unfold depth; omega
    have hp : (n : Int) % 2 = 0 ↔ n % 2 = 0 := by omega
    rw [outDir_eq_of_depth_beta h hd i, hd']
    simp only [hp]
    cases b <;> cases LangtonsAnt.beta w i <;>
      by_cases hn : n % 2 = 0 <;> simp [leaveDir, hn]
  cases b
  · simp only [Bool.false_eq_true, ite_false, betaWord]
    rw [← portWord_not]
    exact portWord_congr hd he
  · exact portWord_congr hd he

theorem predecessor_port_index {P j k : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) {L : Int} {d : Direction}
    (hj : j ∈ UnitDiagonalMatching.arrivals P w (L + UnitDiagonalMatching.layerStep d) d)
    (hk : (trueIdx (portWord hd (L + UnitDiagonalMatching.layerStep d)
      (fun i => decide (inDir w i = d))))[k]? = some (stableRank P w j)) :
    (trueIdx (portWord hd L (fun i => decide (outDir w i = d))))[k]? =
      some (stableRank P w (UnitDiagonalMatching.pred P j)) := by
  have hi := UnitDiagonalMatching.predecessor_mem h.1 hd hj
  have hjP := (UnitDiagonalMatching.mem_arrivals.mp hj).1
  have hs := UnitDiagonalMatching.succ_pred hjP
  obtain ⟨hiP, hiL, hid⟩ := UnitDiagonalMatching.mem_departures.mp hi
  obtain ⟨_, hjL, hjd⟩ := UnitDiagonalMatching.mem_arrivals.mp hj
  have hm := UnitDiagonalMatching.departure_rank_position_eq_arrival_rank_position h.1 hd hi
  rw [hs] at hm
  change (((layerPhases P w L).filter (fun i => decide (outDir w i = d))).filter _).length =
    (((layerPhases P w (L + UnitDiagonalMatching.layerStep d)).filter
      (fun i => decide (inDir w i = d))).filter _).length at hm
  rw [port_position hd (mem_layerPhases.mpr ⟨hiP, hiL⟩) _ (by simpa using hid),
    port_position hd (mem_layerPhases.mpr ⟨hjP, hjL⟩) _ (by simpa using hjd),
    sorted_get_position (pairwise_trueIdx _) hk] at hm
  rw [← hm]
  apply sorted_get_at_position (pairwise_trueIdx _)
  apply mem_trueIdx.mpr
  rw [portWord_at_phase hd (mem_layerPhases.mpr ⟨hiP, hiL⟩)]
  simpa using hid

/-- L19's forced, actual path `A₂ → T → A₀`, including the next departure. -/
theorem first_inner_events {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    ∃ a₂ t a₀,
      a₂ ∈ layerPhases P w (topLayer P w - 1) ∧
      a₀ ∈ layerPhases P w (topLayer P w - 1) ∧
      stableRank P w a₂ = 2 ∧ stableRank P w a₀ = 0 ∧
      UnitDiagonalMatching.succ P a₂ = t ∧ UnitDiagonalMatching.succ P t = a₀ ∧
      inDir w a₂ = .north ∧ outDir w a₂ = .east ∧
      outDir w t = .south ∧ outDir w a₀ = .west := by
  let L := topLayer P w - 1
  have hA := first_inner_two_words h hd
  have hlen : 2 < (layerPhases P w L).length := by
    have hl := portWord_length hd L (LangtonsAnt.alpha w)
    change (alphaWord hd (topLayer P w - 1)).length = _ at hl
    rcases hA with ha | ha <;> rw [ha] at hl <;> simp at hl <;> omega
  let a₂ := phaseAtRank hd L ⟨2, hlen⟩
  have ham : a₂ ∈ layerPhases P w L := phaseAtRank_mem hd L _
  obtain ⟨haP, haL⟩ := mem_layerPhases.mp ham
  have har : stableRank P w a₂ = 2 := phaseAtRank_rank hd L _
  have had : depth P w a₂ = 1 := by unfold depth; dsimp [L] at haL; omega
  have hab : LangtonsAnt.beta w a₂ = true := by
    have hb := betaWord_at_phase hd ham
    rw [betaWord_eq h hd L, har] at hb
    have he : topLayer P w - L = 1 := by dsimp [L]; omega
    rw [he] at hb
    rcases hA with ha | ha <;> change alphaWord hd L = _ at ha <;>
      rw [ha] at hb <;> exact Option.some.inj hb.symm
  have haa : LangtonsAnt.alpha w a₂ = false := by
    have hh := alphaWord_at_phase hd ham
    rw [har] at hh
    rcases hA with ha | ha <;> change alphaWord hd L = _ at ha <;>
      rw [ha] at hh <;> exact Option.some.inj hh.symm
  have hao := outDir_of_depth_odd_beta_true h hd (by rw [had]; decide) hab
  have hai := inDir_of_depth_odd_alpha_false h hd (by rw [had]; decide) haa
  let t := UnitDiagonalMatching.succ P a₂
  have htP : t < P := UnitDiagonalMatching.succ_lt h.period_pos
  have htL : layer (wordPos w t) = topLayer P w := by
    have hs := UnitDiagonalMatching.successor_layer hd haP
    simp only [matching_outDir, hao, UnitDiagonalMatching.layerStep, haL] at hs
    dsimp [t, L] at *
    omega
  have hto : outDir w t = .south := (topLayer_phase_props h hd htP htL).2.2.2
  let a₀ := UnitDiagonalMatching.succ P t
  have hbP : a₀ < P := UnitDiagonalMatching.succ_lt h.period_pos
  have hbL : layer (wordPos w a₀) = L := by
    have hs := UnitDiagonalMatching.successor_layer hd htP
    simpa only [matching_outDir, hto, UnitDiagonalMatching.layerStep, htL,
      Int.add_neg_one] using hs
  have hbm := mem_layerPhases.mpr ⟨hbP, hbL⟩
  have hba : LangtonsAnt.alpha w a₀ = true := by
    have hs := UnitDiagonalMatching.successor_heading h.1 htP
    simp only [matching_inDir, matching_outDir, hto] at hs
    simp [LangtonsAnt.alpha, show inDir w a₀ = .south from hs]
  have hbr : stableRank P w a₀ = 0 := by
    have hh := alphaWord_at_phase hd hbm
    rw [hba] at hh
    have hm := mem_trueIdx.mpr hh
    rcases hA with ha | ha <;> change alphaWord hd L = _ at ha <;>
      rw [ha] at hm <;> simpa [trueIdx] using hm
  have hbb : LangtonsAnt.beta w a₀ = false := by
    have hb := betaWord_at_phase hd hbm
    rw [betaWord_eq h hd L, hbr] at hb
    have he : topLayer P w - L = 1 := by dsimp [L]; omega
    rw [he] at hb
    rcases hA with ha | ha <;> change alphaWord hd L = _ at ha <;>
      rw [ha] at hb <;> exact Option.some.inj hb.symm
  have hbd : depth P w a₀ = 1 := by unfold depth; dsimp [L] at hbL; omega
  exact ⟨a₂, t, a₀, ham, hbm, har, hbr, rfl, rfl, hai, hao, hto,
    outDir_of_depth_odd_beta_false h hd (by rw [hbd]; decide) hbb⟩

private theorem path_succ {P len : Nat} (p : ContinuousPhasePath P len)
    {r : Nat} (hr : r < len) :
    p.phase (r + 1) = UnitDiagonalMatching.succ P (p.phase r) := by
  rcases p.successor hr with ⟨hs, _⟩ | ⟨he, hz, _⟩
  · rw [UnitDiagonalMatching.succ, ← hs, Nat.mod_eq_of_lt (p.phase_lt _ (by omega))]
  · simp [UnitDiagonalMatching.succ, he, hz]

/-- A four-edge physical first return advances rank by one. Every edge is supplied
as an actual cyclic successor; there is no assumption that the period exceeds four. -/
theorem four_step_return_rank {P i₀ i₁ i₂ i₃ i₄ : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i₀ < P)
    (hs₀ : UnitDiagonalMatching.succ P i₀ = i₁)
    (hs₁ : UnitDiagonalMatching.succ P i₁ = i₂)
    (hs₂ : UnitDiagonalMatching.succ P i₂ = i₃)
    (hs₃ : UnitDiagonalMatching.succ P i₃ = i₄)
    (d₀ d₁ d₂ d₃ : Direction)
    (hd₀ : outDir w i₀ = d₀) (hd₁ : outDir w i₁ = d₁)
    (hd₂ : outDir w i₂ = d₂) (hd₃ : outDir w i₃ = d₃)
    (hret : ∀ q, FirstReturn q [d₀, d₁, d₂, d₃]) :
    stableRank P w i₄ = stableRank P w i₀ + 1 := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ 4
  have hp₀ : p.phase 0 = i₀ := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have hp₁ : p.phase 1 = i₁ := by rw [path_succ p (by decide : 0 < 4), hp₀, hs₀]
  have hp₂ : p.phase 2 = i₂ := by rw [path_succ p (by decide : 1 < 4), hp₁, hs₁]
  have hp₃ : p.phase 3 = i₃ := by rw [path_succ p (by decide : 2 < 4), hp₂, hs₂]
  have hp₄ : p.phase 4 = i₄ := by rw [path_succ p (by decide : 3 < 4), hp₃, hs₃]
  have step (r : Nat) (hr : r < 4) : p.pos w (r + 1) = move (p.pos w r) (outDir w (p.phase r)) :=
    p.pos_step hr
  have hx₁ : p.pos w 1 = move (p.pos w 0) d₀ := by rw [step 0 (by decide), hp₀, hd₀]
  have hx₂ : p.pos w 2 = move (move (p.pos w 0) d₀) d₁ := by
    rw [step 1 (by decide), hp₁, hd₁, hx₁]
  have hx₃ : p.pos w 3 = move (move (move (p.pos w 0) d₀) d₁) d₂ := by
    rw [step 2 (by decide), hp₂, hd₂, hx₂]
  have hx₄ : p.pos w 4 = walk (p.pos w 0) [d₀, d₁, d₂, d₃] := by
    rw [step 3 (by decide), hp₃, hd₃, hx₃]; rfl
  obtain ⟨hclose, hfirst⟩ := (firstReturn_iff _ _).mp (hret (p.pos w 0))
  have hh := p.firstReturn_rank hd (by decide : 0 < 4) (hx₄.trans hclose) (by
    intro r hr hr'
    rcases (show r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl
    · simpa only [hx₁, List.take, walk] using hfirst 1 (by decide) (by simp)
    · simpa only [hx₂, List.take, walk] using hfirst 2 (by decide) (by simp)
    · simpa only [hx₃, List.take, walk] using hfirst 3 (by decide) (by simp))
  simpa only [hp₀, hp₄] using hh

/-- L20: the NESW return yields the first-to-second upper-port adjacency on B. -/
theorem second_inner_adjacency {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    ∃ a b,
      (trueIdx (alphaWord hd (topLayer P w - 2)))[0]? = some a ∧
      (trueIdx (betaWord hd (topLayer P w - 2)))[1]? = some b ∧ a = b + 1 := by
  obtain ⟨a₂, t, a₀, ha₂, ha₀, hr₂, hr₀, hs₂, hst, hi₂, ho₂, hot, ho₀⟩ :=
    first_inner_events h hd
  have hA := first_inner_two_words h hd
  have hβA : betaWord hd (topLayer P w - 1) =
      beta (alphaWord hd (topLayer P w - 1)) true := by
    have hb := betaWord_eq h hd (topLayer P w - 1)
    have he : topLayer P w - (topLayer P w - 1) = 1 := by omega
    rw [he] at hb
    exact hb
  have hWA : portWord hd (topLayer P w - 1) (fun i => decide (outDir w i = .west)) =
      (betaWord hd (topLayer P w - 1)).map (!·) := outgoing_portWord h hd 1 false
  have hNA : portWord hd (topLayer P w - 1) (fun i => decide (inDir w i = .north)) =
      (alphaWord hd (topLayer P w - 1)).map (!·) := incoming_portWord h hd 1 false
  have hWB : portWord hd (topLayer P w - 2) (fun i => decide (inDir w i = .west)) =
      alphaWord hd (topLayer P w - 2) := incoming_portWord h hd 2 true
  have hNB : portWord hd (topLayer P w - 2) (fun i => decide (outDir w i = .north)) =
      betaWord hd (topLayer P w - 2) := outgoing_portWord h hd 2 true
  have hLdown : topLayer P w - 1 + UnitDiagonalMatching.layerStep .west =
      topLayer P w - 2 := by simp only [UnitDiagonalMatching.layerStep]; omega
  have hLup : topLayer P w - 2 + UnitDiagonalMatching.layerStep .north =
      topLayer P w - 1 := by simp only [UnitDiagonalMatching.layerStep]; omega
  have ha₀d : a₀ ∈ UnitDiagonalMatching.departures P w (topLayer P w - 1) .west :=
    UnitDiagonalMatching.mem_departures.mpr
      ⟨(mem_layerPhases.mp ha₀).1, (mem_layerPhases.mp ha₀).2, ho₀⟩
  have hp := successor_port_index h hd ha₀d (k := 0) (by
    rw [hWA, hβA, hr₀]
    rcases hA with he | he <;> rw [he] <;> rfl)
  rw [hLdown, hWB] at hp
  have ha₂a : a₂ ∈ UnitDiagonalMatching.arrivals P w
      (topLayer P w - 2 + UnitDiagonalMatching.layerStep .north) .north := by
    rw [hLup]
    exact UnitDiagonalMatching.mem_arrivals.mpr
      ⟨(mem_layerPhases.mp ha₂).1, (mem_layerPhases.mp ha₂).2, hi₂⟩
  have hq := predecessor_port_index h hd ha₂a (k := 1) (by
    rw [hLup, hNA, hr₂]
    rcases hA with he | he <;> rw [he] <;> rfl)
  rw [hNB] at hq
  let b := UnitDiagonalMatching.pred P a₂
  have hbP : b < P := UnitDiagonalMatching.pred_lt (mem_layerPhases.mp ha₂).1
  have hbo : outDir w b = .north :=
    (UnitDiagonalMatching.mem_departures.mp (UnitDiagonalMatching.predecessor_mem h.1 hd ha₂a)).2.2
  have hs : UnitDiagonalMatching.succ P b = a₂ :=
    UnitDiagonalMatching.succ_pred (mem_layerPhases.mp ha₂).1
  have hret := four_step_return_rank hd hbP hs hs₂ hst rfl
    .north .east .south .west hbo ho₂ hot ho₀ firstReturn_NESW
  exact ⟨_, _, hp, hq, hret⟩

/-- L21-L22 for actual layer words, with no bound on the original period. -/
theorem second_inner_two_words {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    alphaWord hd (topLayer P w - 1) = [true, false, false, false] ∧
      (alphaWord hd (topLayer P w - 2) = W8 ∨ alphaWord hd (topLayer P w - 2) = W9) := by
  have hA := first_inner_two_words h hd
  have hc := cut_down_count h hd (topLayer P w - 1)
  have he : topLayer P w - 1 - 1 = topLayer P w - 2 := by omega
  rw [he, (first_inner_counts h hd).2] at hc
  let c := countTrue (alphaWord hd (topLayer P w - 2))
  have hc23 : c = 2 ∨ c = 3 := by
    have hl := portWord_length hd (topLayer P w - 1) (LangtonsAnt.alpha w)
    change (alphaWord hd (topLayer P w - 1)).length = _ at hl
    rcases hA with ha | ha
    · rw [ha] at hl; left; dsimp [c]; simp at hl; omega
    · rw [ha] at hl; right; dsimp [c]; simp at hl; omega
  have hβB : betaWord hd (topLayer P w - 2) =
      beta (alphaWord hd (topLayer P w - 2)) false := by
    have hb := betaWord_eq h hd (topLayer P w - 2)
    have he' : topLayer P w - (topLayer P w - 2) = 2 := by omega
    rw [he'] at hb
    exact hb
  have hqcount : countTrue (beta (alphaWord hd (topLayer P w - 2)) false) = c := by
    rw [← hβB]
    exact (layer_counts_eq h hd (by omega : topLayer P w - 2 ≤ topLayer P w)).symm
  obtain ⟨a, b, hp, hq, hab⟩ := second_inner_adjacency h hd
  rw [hβB] at hq
  have hh := even_two_or_three (alphaWord hd (topLayer P w - 2)) c a b
    (trueIdx_length _) (by rw [trueIdx_length]; exact hqcount) hc23
    (by rw [trueIdx_length, hqcount]; omega)
    (by rw [trueIdx_length]; change 1 ≤ c; omega) hp hq hab
  refine ⟨?_, hh.2⟩
  rcases hA with ha | ha
  · have hl := portWord_length hd (topLayer P w - 1) (LangtonsAnt.alpha w)
    change (alphaWord hd (topLayer P w - 1)).length = _ at hl
    rw [ha] at hl
    have hc3 : countTrue (alphaWord hd (topLayer P w - 2)) = 3 := hh.1
    simp only [List.length_cons, List.length_nil] at hl
    omega
  · exact ha

end UnitDiagonal
