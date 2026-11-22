import TwoCellDiagonalExtremal
import UnitDiagonalWords
import UnitDiagonalInterleave

/-!
# Adjacent-lane first returns and no three consecutive `1000` lanes for diagonal-multiple drift `(m, -m)`

For an arbitrary positive integer `m`, period `P > 0`, and `ConsistentWord P w` with full period
displacement `(m, -m)` — with **no minimality assumption** and **no global top-layer occupancy
assumption** — we formalize:

1. **General anti-diagonal (`layer v = 0`) rank-ordered class port words and directed matching**
   built on `LangtonsAnt.Drift.*` (full translation classes, `stableRank`, `path_firstReturn_rank`,
   and ordered departure/arrival matching).
2. **Adjacent-lane first-return relation (Target 1)**: if adjacent first-inner-layer lanes
   `r` and `r + 1` have rank-ordered arrival words `a, b ∈ {100, 1000, 001, 0010}`, then the
   second-inner-layer lane `r` has upper arrival/departure rank tables `p, q` satisfying
   `p.length = b.length - 1`, `q.length = a.length - 1`, and `p[arrPortIdx b] = q[depPortIdx a] + 1`
   (early `100`/`1000`: `i = 0, j = 1`; late `001`/`0010`: `i = 1, j = 0`). As immediate
   corollaries, `(100, 100)` and `(100, 1000)` are forbidden adjacent first-inner-layer pairs, and
   `(1000, 1000)` forces `W8` or `W9` on the second-inner-layer lane.
3. **No three consecutive `1000` lanes (Target 2)**: no lane `r` can satisfy
   `α_r = α_{r+1} = α_{r+2} = 1000` on the first inner layer `topLayer P w - 1`.
4. **Non-vacuity on the rotated standard 104-step highway (Target 3)**: `stdHighwaySE`
   (`P = 104`, drift `(2, -2)`, `m = 2`) has first-inner-layer lane words `001` and `1000`,
   satisfying Target 1 on both lanes while witnessing non-vacuity of Target 2.

Every proof is checked purely by the Lean kernel (no `sorry`, no `axiom`, no `native_decide`).
-/

namespace LangtonsAnt
namespace DiagonalMultipleLanes

/-! ## 1. Diagonal-multiple drift `(m, -m)` and lane representatives -/

/-- Full period drift vector `(m, -m)` for `m : Nat`. -/
def diagDrift (m : Nat) : Point := ((m : Int), -(m : Int))

/-- Representative grid cell `(r, t - r)` for transverse layer `t = x + y` and lane `r`. -/
def laneCell (t r : Int) : Point := (r, t - r)

theorem diagDrift_ne_zero {m : Nat} (hm : 0 < m) : diagDrift m ≠ (0, 0) := by
  intro h
  have hx := congrArg Prod.fst h
  simp only [diagDrift] at hx
  omega

theorem layer_diagDrift (m : Nat) : layer (diagDrift m) = 0 := by
  simp only [layer, weight, diagDrift]
  omega

theorem layer_laneCell (t r : Int) : layer (laneCell t r) = t := by
  simp only [layer, weight, laneCell]
  omega

theorem move_laneCell_north (t r : Int) :
    move (laneCell t r) .north = laneCell (t + 1) r := by
  apply Prod.ext <;> simp only [laneCell, move] <;> omega

theorem move_laneCell_south (t r : Int) :
    move (laneCell t r) .south = laneCell (t - 1) r := by
  apply Prod.ext <;> simp only [laneCell, move] <;> omega

theorem move_laneCell_east (t r : Int) :
    move (laneCell t r) .east = laneCell (t + 1) (r + 1) := by
  apply Prod.ext <;> simp only [laneCell, move] <;> omega

theorem move_laneCell_west (t r : Int) :
    move (laneCell t r) .west = laneCell (t - 1) (r - 1) := by
  apply Prod.ext <;> simp only [laneCell, move] <;> omega

theorem sameClass_diagDrift_iff {m : Nat} (hm : 0 < m) (p q : Point) :
    Drift.SameClass (diagDrift m) p q ↔
      layer p = layer q ∧ p.1 % (m : Int) = q.1 % (m : Int) := by
  have hm' : (m : Int) ≠ 0 := by omega
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [layer, weight, addPoint, scalePoint, diagDrift, Int.mul_neg]
      omega
    · simp only [addPoint, scalePoint, diagDrift]
      rw [Int.add_mul_emod_self_right]
  · rintro ⟨hl, hmod⟩
    refine ⟨(q.1 - p.1) / (m : Int), ?_⟩
    have hsub : (q.1 - p.1) % (m : Int) = 0 := by
      rw [Int.sub_emod, ← hmod, Int.sub_self, Int.zero_emod]
    have hdvd : (m : Int) ∣ (q.1 - p.1) := Int.dvd_of_emod_eq_zero hsub
    have hmul : (q.1 - p.1) / (m : Int) * (m : Int) = q.1 - p.1 :=
      Int.ediv_mul_cancel hdvd
    simp only [layer, weight] at hl
    apply Prod.ext
    · simp only [addPoint, scalePoint, diagDrift]
      omega
    · simp only [addPoint, scalePoint, diagDrift, Int.mul_neg]
      omega

theorem sameClass_laneCell_iff {m : Nat} (hm : 0 < m) (t₁ r₁ t₂ r₂ : Int) :
    Drift.SameClass (diagDrift m) (laneCell t₁ r₁) (laneCell t₂ r₂) ↔
      t₁ = t₂ ∧ r₁ % (m : Int) = r₂ % (m : Int) := by
  rw [sameClass_diagDrift_iff hm, layer_laneCell, layer_laneCell]
  rfl

theorem sameClass_laneCell_add_m (m : Nat) (t r : Int) :
    Drift.SameClass (diagDrift m) (laneCell t r) (laneCell t (r + (m : Int))) := by
  refine ⟨1, ?_⟩
  apply Prod.ext <;> simp only [laneCell, addPoint, scalePoint, diagDrift] <;> omega

/-! ## 2. Anti-diagonal (`layer v = 0`) port XOR and rank-ordered class port words -/

theorem depth_even_iff_layer_odd_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (i : Nat) :
    depth P w i % 2 = 0 ↔ layer (wordPos w i) % 2 = 1 := by
  have ht := TwoCellDiagonal.topLayer_odd_of_layer_zero h hlv
  unfold depth
  omega

theorem inDir_horizontal_eq_depth_even_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (i : Nat) :
    (inDir w i).horizontal = decide (depth P w i % 2 = 0) := by
  rw [inDir_horizontal_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (depth_even_iff_layer_odd_of_layer_zero h hlv i).symm

theorem depth_odd_decide_eq_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (i : Nat) :
    decide (depth P w i % 2 = 1) = !(inDir w i).horizontal := by
  rw [inDir_horizontal_eq_depth_even_of_layer_zero h hlv i]
  by_cases he : depth P w i % 2 = 0
  · simp [he]
  · have ho : depth P w i % 2 = 1 := by omega
    simp [ho]

theorem inDir_eq_of_depth_alpha_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (i : Nat) :
    inDir w i =
      if depth P w i % 2 = 0 then
        if LangtonsAnt.alpha w i then .west else .east
      else
        if LangtonsAnt.alpha w i then .south else .north := by
  have hhor := inDir_horizontal_eq_depth_even_of_layer_zero h hlv i
  unfold LangtonsAnt.alpha
  cases hd' : inDir w i <;> rw [hd'] at hhor <;>
    simp [Direction.horizontal] at hhor ⊢ <;> simp [hhor]

theorem outDir_eq_of_depth_beta_of_layer_zero {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (i : Nat) :
    outDir w i =
      if depth P w i % 2 = 0 then
        if LangtonsAnt.beta w i then .north else .south
      else
        if LangtonsAnt.beta w i then .east else .west := by
  have hhor := inDir_horizontal_eq_depth_even_of_layer_zero h hlv i
  unfold LangtonsAnt.beta outDir
  cases hd' : inDir w i <;> rw [hd'] at hhor <;> cases w i <;>
    simp [Direction.horizontal, turn, Direction.left, Direction.right] at hhor ⊢ <;>
    simp [hhor]

theorem beta_eq_xor_of_layer_zero {P i : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hlv : layer (wordDrift P w) = 0) (hi : i < P) :
    LangtonsAnt.beta w i =
      xor (xor (LangtonsAnt.alpha w i) (decide (Drift.stableRank P w i % 2 = 1)))
        (decide (depth P w i % 2 = 1)) := by
  rw [← Drift.consistentWord_stableRank_color h hi, depth_odd_decide_eq_of_layer_zero h hlv i]
  unfold LangtonsAnt.beta outDir LangtonsAnt.alpha
  cases inDir w i <;> cases w i <;> rfl

/-- Computable lookup of the unique phase in translation class `c` with `stableRank = k`. -/
def classPhaseAtRank (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (k : Nat) : Nat :=
  ((Drift.classPhases v P w c).find? (fun i => decide (Drift.stableRank P w i = k))).getD 0

/-- All phases in translation class `c`, listed in increasing `stableRank` order. -/
def classRankedPhases (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) : List Nat :=
  (List.range (Drift.classPhases v P w c).length).map (classPhaseAtRank v P w c)

/-- A phase observable sampled across translation class `c` in `stableRank` order. -/
def classPortWord (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (f : Nat → Bool) :
    List Bool :=
  (classRankedPhases v P w c).map f

/-- Rank-ordered arrival-port word `α` on translation class `c`. -/
def classAlphaWord (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) : List Bool :=
  classPortWord v P w c (LangtonsAnt.alpha w)

/-- Rank-ordered departure-port word `β` on translation class `c`. -/
def classBetaWord (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) : List Bool :=
  classPortWord v P w c (LangtonsAnt.beta w)

/-- Rank-ordered arrival-port word `α` on layer `t`, lane `r` for drift `(m, -m)`. -/
def laneAlpha (m P : Nat) (w : Nat → Bool) (t r : Int) : List Bool :=
  classAlphaWord (diagDrift m) P w (laneCell t r)

/-- Rank-ordered departure-port word `β` on layer `t`, lane `r` for drift `(m, -m)`. -/
def laneBeta (m P : Nat) (w : Nat → Bool) (t r : Int) : List Bool :=
  classBetaWord (diagDrift m) P w (laneCell t r)

theorem classPhaseAtRank_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool) (k : Nat)
    (h : Drift.SameClass v c₁ c₂) :
    classPhaseAtRank v P w c₁ k = classPhaseAtRank v P w c₂ k := by
  simp only [classPhaseAtRank, Drift.classPhases_congr P w h]

theorem classRankedPhases_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool)
    (h : Drift.SameClass v c₁ c₂) :
    classRankedPhases v P w c₁ = classRankedPhases v P w c₂ := by
  unfold classRankedPhases
  rw [Drift.classPhases_congr P w h]
  apply List.map_congr_left
  intro k _
  exact classPhaseAtRank_congr P w k h

theorem classPortWord_congr_class {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool) (f : Nat → Bool)
    (h : Drift.SameClass v c₁ c₂) :
    classPortWord v P w c₁ f = classPortWord v P w c₂ f := by
  simp only [classPortWord, classRankedPhases_congr P w h]

theorem classAlphaWord_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool)
    (h : Drift.SameClass v c₁ c₂) :
    classAlphaWord v P w c₁ = classAlphaWord v P w c₂ :=
  classPortWord_congr_class P w _ h

theorem classBetaWord_congr {v c₁ c₂ : Point} (P : Nat) (w : Nat → Bool)
    (h : Drift.SameClass v c₁ c₂) :
    classBetaWord v P w c₁ = classBetaWord v P w c₂ :=
  classPortWord_congr_class P w _ h

theorem laneAlpha_periodic (m P : Nat) (w : Nat → Bool) (t r : Int) :
    laneAlpha m P w t (r + (m : Int)) = laneAlpha m P w t r :=
  (classAlphaWord_congr P w (sameClass_laneCell_add_m m t r)).symm

theorem laneBeta_periodic (m P : Nat) (w : Nat → Bool) (t r : Int) :
    laneBeta m P w t (r + (m : Int)) = laneBeta m P w t r :=
  (classBetaWord_congr P w (sameClass_laneCell_add_m m t r)).symm

theorem laneAlpha_congr_mod {m P : Nat} (hm : 0 < m) (w : Nat → Bool) (t r₁ r₂ : Int)
    (hmod : r₁ % (m : Int) = r₂ % (m : Int)) :
    laneAlpha m P w t r₁ = laneAlpha m P w t r₂ :=
  classAlphaWord_congr P w ((sameClass_laneCell_iff hm t r₁ t r₂).mpr ⟨rfl, hmod⟩)

theorem classPhaseAtRank_spec {v c : Point} {P k : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hk : k < (Drift.classPhases v P w c).length) :
    classPhaseAtRank v P w c k ∈ Drift.classPhases v P w c ∧
      Drift.stableRank P w (classPhaseAtRank v P w c k) = k := by
  obtain ⟨i, hiC, hir⟩ := Drift.stableRank_surjective_on_class hd hv hk
  cases hf : (Drift.classPhases v P w c).find? (fun j => decide (Drift.stableRank P w j = k)) with
  | none =>
    have hnone := List.find?_eq_none.mp hf i hiC
    simp [hir] at hnone
  | some a =>
    have hmem : a ∈ Drift.classPhases v P w c := List.mem_of_find?_eq_some hf
    have hrdec := List.find?_some (p := fun j => decide (Drift.stableRank P w j = k)) hf
    have hr : Drift.stableRank P w a = k := of_decide_eq_true hrdec
    simpa only [classPhaseAtRank, hf, Option.getD_some] using And.intro hmem hr

theorem classPhaseAtRank_mem {v c : Point} {P k : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hk : k < (Drift.classPhases v P w c).length) :
    classPhaseAtRank v P w c k ∈ Drift.classPhases v P w c :=
  (classPhaseAtRank_spec hd hv hk).1

theorem classPhaseAtRank_rank {v c : Point} {P k : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hk : k < (Drift.classPhases v P w c).length) :
    Drift.stableRank P w (classPhaseAtRank v P w c k) = k :=
  (classPhaseAtRank_spec hd hv hk).2

theorem classPhaseAtRank_eq {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ Drift.classPhases v P w c) :
    classPhaseAtRank v P w c (Drift.stableRank P w i) = i := by
  have hlt := Drift.stableRank_lt_class_length hd hv hi
  exact Drift.stableRank_injective_on_class hd hv
    (classPhaseAtRank_mem hd hv hlt) hi (classPhaseAtRank_rank hd hv hlt)

@[simp] theorem classRankedPhases_length (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) :
    (classRankedPhases v P w c).length = (Drift.classPhases v P w c).length := by
  simp [classRankedPhases]

@[simp] theorem classPortWord_length (v : Point) (P : Nat) (w : Nat → Bool) (c : Point)
    (f : Nat → Bool) :
    (classPortWord v P w c f).length = (Drift.classPhases v P w c).length := by
  simp [classPortWord]

theorem classRankedPhases_perm {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    (classRankedPhases v P w c).Perm (Drift.classPhases v P w c) := by
  have hn : (classRankedPhases v P w c).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj hij
    simp only [classRankedPhases_length] at hi hj
    have h1 := congrArg (Drift.stableRank P w) hij
    simp only [classRankedPhases, List.getElem_map, List.getElem_range] at h1
    rw [classPhaseAtRank_rank hd hv hi, classPhaseAtRank_rank hd hv hj] at h1
    exact h1
  apply (List.perm_ext_iff_of_nodup hn (Drift.classPhases_nodup v P w c)).mpr
  intro i
  simp only [classRankedPhases, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact classPhaseAtRank_mem hd hv hk
  · intro hi
    exact ⟨Drift.stableRank P w i, Drift.stableRank_lt_class_length hd hv hi,
      classPhaseAtRank_eq hd hv hi⟩

theorem classPortWord_getElem? {v c : Point} {P k : Nat} {w : Nat → Bool}
    (f : Nat → Bool) (hk : k < (Drift.classPhases v P w c).length) :
    (classPortWord v P w c f)[k]? = some (f (classPhaseAtRank v P w c k)) := by
  simp [classPortWord, classRankedPhases, hk]

theorem classPortWord_at_phase {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ Drift.classPhases v P w c) (f : Nat → Bool) :
    (classPortWord v P w c f)[Drift.stableRank P w i]? = some (f i) := by
  have hlt := Drift.stableRank_lt_class_length hd hv hi
  rw [classPortWord_getElem? f hlt, classPhaseAtRank_eq hd hv hi]

theorem classAlphaWord_at_phase {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ Drift.classPhases v P w c) :
    (classAlphaWord v P w c)[Drift.stableRank P w i]? = some (LangtonsAnt.alpha w i) :=
  classPortWord_at_phase hd hv hi _

theorem classBetaWord_at_phase {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ Drift.classPhases v P w c) :
    (classBetaWord v P w c)[Drift.stableRank P w i]? = some (LangtonsAnt.beta w i) :=
  classPortWord_at_phase hd hv hi _

theorem classBetaWord_eq {v c : Point} {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hlv : layer v = 0) :
    classBetaWord v P w c =
      UnitDiagonal.beta (classAlphaWord v P w c) (decide ((topLayer P w - layer c) % 2 = 1)) := by
  have hlv' : layer (wordDrift P w) = 0 := by rw [hd]; exact hlv
  apply List.ext_getElem?
  intro k
  by_cases hk : k < (Drift.classPhases v P w c).length
  · have hm := Drift.mem_classPhases.mp (classPhaseAtRank_mem hd hv hk)
    have hlay : layer (wordPos w (classPhaseAtRank v P w c k)) = layer c :=
      TwoCellDiagonal.layer_eq_of_sameClass hlv hm.2
    rw [UnitDiagonal.beta_spec]
    change (classPortWord v P w c (LangtonsAnt.beta w))[k]? =
      ((classPortWord v P w c (LangtonsAnt.alpha w))[k]?).map _
    rw [classPortWord_getElem? _ hk, classPortWord_getElem? _ hk]
    simp only [Option.map_some]
    rw [beta_eq_xor_of_layer_zero h hlv' hm.1, classPhaseAtRank_rank hd hv hk]
    simp only [depth, hlay]
  · have ha : (classAlphaWord v P w c).length ≤ k := by simp [classAlphaWord]; omega
    have hb : (classBetaWord v P w c).length ≤ k := by simp [classBetaWord]; omega
    rw [List.getElem?_eq_none hb,
      List.getElem?_eq_none (by rw [UnitDiagonal.beta_length]; exact ha)]

private theorem countTrue_map (xs : List Nat) (f : Nat → Bool) :
    UnitDiagonal.countTrue (xs.map f) = (xs.filter f).length := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases hf : f i <;> simp [UnitDiagonal.countTrue, hf, ih] <;> omega

theorem classPortWord_count {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (f : Nat → Bool) :
    UnitDiagonal.countTrue (classPortWord v P w c f) =
      ((Drift.classPhases v P w c).filter f).length := by
  rw [classPortWord, countTrue_map]
  exact ((classRankedPhases_perm hd hv).filter f).length_eq

theorem classPortWord_congr_fn {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) {f g : Nat → Bool}
    (he : ∀ i ∈ Drift.classPhases v P w c, f i = g i) :
    classPortWord v P w c f = classPortWord v P w c g := by
  apply List.map_congr_left
  intro i hi
  exact he i ((classRankedPhases_perm hd hv).mem_iff.mp hi)

theorem classPortWord_not (v : Point) (P : Nat) (w : Nat → Bool) (c : Point) (f : Nat → Bool) :
    classPortWord v P w c (fun i => !f i) = (classPortWord v P w c f).map (!·) := by
  simp [classPortWord, List.map_map, Function.comp_def]

def enterDir (n : Nat) (b : Bool) : Direction :=
  if n % 2 = 0 then (if b then .west else .east) else (if b then .south else .north)

def leaveDir (n : Nat) (b : Bool) : Direction :=
  if n % 2 = 0 then (if b then .north else .south) else (if b then .east else .west)

theorem incoming_classPortWord {v c : Point} {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hlv : layer v = 0)
    (n : Nat) (hc : layer c = topLayer P w - (n : Int)) (b : Bool) :
    classPortWord v P w c (fun i => decide (inDir w i = enterDir n b)) =
      if b then classAlphaWord v P w c else (classAlphaWord v P w c).map (!·) := by
  have hlv' : layer (wordDrift P w) = 0 := by rw [hd]; exact hlv
  have he (i : Nat) (hi : i ∈ Drift.classPhases v P w c) :
      decide (inDir w i = enterDir n b) =
        if b then LangtonsAnt.alpha w i else !LangtonsAnt.alpha w i := by
    have hl : layer (wordPos w i) = layer c :=
      TwoCellDiagonal.layer_eq_of_sameClass hlv (Drift.mem_classPhases.mp hi).2
    have hdep : depth P w i = (n : Int) := by unfold depth; omega
    have hp : (n : Int) % 2 = 0 ↔ n % 2 = 0 := by omega
    rw [inDir_eq_of_depth_alpha_of_layer_zero h hlv' i, hdep]
    simp only [hp]
    cases b <;> cases LangtonsAnt.alpha w i <;>
      by_cases hn : n % 2 = 0 <;> simp [enterDir, hn]
  cases b
  · simp only [Bool.false_eq_true, ite_false, classAlphaWord]
    rw [← classPortWord_not]
    exact classPortWord_congr_fn hd hv he
  · exact classPortWord_congr_fn hd hv he

theorem outgoing_classPortWord {v c : Point} {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hlv : layer v = 0)
    (n : Nat) (hc : layer c = topLayer P w - (n : Int)) (b : Bool) :
    classPortWord v P w c (fun i => decide (outDir w i = leaveDir n b)) =
      if b then classBetaWord v P w c else (classBetaWord v P w c).map (!·) := by
  have hlv' : layer (wordDrift P w) = 0 := by rw [hd]; exact hlv
  have he (i : Nat) (hi : i ∈ Drift.classPhases v P w c) :
      decide (outDir w i = leaveDir n b) =
        if b then LangtonsAnt.beta w i else !LangtonsAnt.beta w i := by
    have hl : layer (wordPos w i) = layer c :=
      TwoCellDiagonal.layer_eq_of_sameClass hlv (Drift.mem_classPhases.mp hi).2
    have hdep : depth P w i = (n : Int) := by unfold depth; omega
    have hp : (n : Int) % 2 = 0 ↔ n % 2 = 0 := by omega
    rw [outDir_eq_of_depth_beta_of_layer_zero h hlv' i, hdep]
    simp only [hp]
    cases b <;> cases LangtonsAnt.beta w i <;>
      by_cases hn : n % 2 = 0 <;> simp [leaveDir, hn]
  cases b
  · simp only [Bool.false_eq_true, ite_false, classBetaWord]
    rw [← classPortWord_not]
    exact classPortWord_congr_fn hd hv he
  · exact classPortWord_congr_fn hd hv he

/-! ## 3. Directed port matching and physical first returns for arbitrary nonzero drift -/

private theorem trueIdx_nodup (xs : List Bool) : (UnitDiagonal.trueIdx xs).Nodup :=
  (UnitDiagonal.pairwise_trueIdx xs).imp (fun h => Nat.ne_of_lt h)

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

theorem class_port_position {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hi : i ∈ Drift.classPhases v P w c) (f : Nat → Bool) (hf : f i = true) :
    (((Drift.classPhases v P w c).filter f).filter
      (fun j => decide (Drift.stableRank P w j < Drift.stableRank P w i))).length =
    ((UnitDiagonal.trueIdx (classPortWord v P w c f)).filter
      (fun r => decide (r < Drift.stableRank P w i))).length := by
  apply ordered_bijection_position _ _ (Drift.stableRank P w)
    (fun j k => Drift.stableRank P w j < Drift.stableRank P w k) (· < ·)
    ((Drift.classPhases_nodup v P w c).filter f) (trueIdx_nodup _)
    (fun _ hj _ hk => Drift.stableRank_injective_on_class hd hv
      (List.mem_filter.mp hj).1 (List.mem_filter.mp hk).1) _
    (fun _ _ _ _ => Iff.rfl) (List.mem_filter.mpr ⟨hi, hf⟩)
  intro r
  constructor
  · intro hr
    have hval := UnitDiagonal.mem_trueIdx.mp hr
    have hrlt : r < (Drift.classPhases v P w c).length := by
      simpa only [classPortWord_length] using UnitDiagonal.lt_length_of_getElem? hval
    have hj := classPhaseAtRank_mem hd hv hrlt
    have hf' := classPortWord_getElem? (v := v) (P := P) (w := w) (c := c) f hrlt
    rw [hval] at hf'
    exact ⟨classPhaseAtRank v P w c r, List.mem_filter.mpr ⟨hj, (Option.some.inj hf').symm⟩,
      classPhaseAtRank_rank hd hv hrlt⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hjm, hjf⟩ := List.mem_filter.mp hj
    apply UnitDiagonal.mem_trueIdx.mpr
    rw [classPortWord_at_phase hd hv hjm f, hjf]

private theorem drift_inDir_eq (w : Nat → Bool) (i : Nat) : Drift.inDir w i = inDir w i := rfl
private theorem drift_outDir_eq (w : Nat → Bool) (i : Nat) : Drift.outDir w i = outDir w i := rfl
private theorem drift_succ_pred {P j : Nat} (hj : j < P) : Drift.succ P (Drift.pred P j) = j :=
  UnitDiagonalMatching.succ_pred hj

theorem class_successor_port_index {v c c' : Point} {P i k : Nat} {w : Nat → Bool}
    {d : Direction} (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : Drift.SameClass v (move c d) c') (hi : i ∈ Drift.departures v P w c d)
    (hk : (UnitDiagonal.trueIdx (classPortWord v P w c (fun j => decide (outDir w j = d))))[k]? =
      some (Drift.stableRank P w i)) :
    (UnitDiagonal.trueIdx (classPortWord v P w c' (fun j => decide (inDir w j = d))))[k]? =
      some (Drift.stableRank P w (Drift.succ P i)) := by
  have hj := (Drift.successor_mem_iff h.1 hd (Drift.mem_departures.mp hi).1).mpr hi
  rw [Drift.arrivals_congr P w d ht] at hj
  obtain ⟨hiP, hic, hid⟩ := Drift.mem_departures.mp hi
  obtain ⟨hjP, hjc, hjd⟩ := Drift.mem_arrivals.mp hj
  rw [drift_outDir_eq] at hid
  rw [drift_inDir_eq] at hjd
  have hm := Drift.departure_rank_position_eq_arrival_rank_position_of_target h.1 hd hv ht hi
  change (((Drift.classPhases v P w c).filter (fun j => decide (outDir w j = d))).filter _).length =
    (((Drift.classPhases v P w c').filter (fun j => decide (inDir w j = d))).filter _).length at hm
  rw [class_port_position hd hv (Drift.mem_classPhases.mpr ⟨hiP, hic⟩) _ (by simpa using hid),
    class_port_position hd hv (Drift.mem_classPhases.mpr ⟨hjP, hjc⟩) _ (by simpa using hjd),
    sorted_get_position (UnitDiagonal.pairwise_trueIdx _) hk] at hm
  rw [hm]
  apply sorted_get_at_position (UnitDiagonal.pairwise_trueIdx _)
  apply UnitDiagonal.mem_trueIdx.mpr
  rw [classPortWord_at_phase hd hv (Drift.mem_classPhases.mpr ⟨hjP, hjc⟩)]
  simpa using hjd

theorem class_predecessor_port_index {v c c' : Point} {P j k : Nat} {w : Nat → Bool}
    {d : Direction} (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : Drift.SameClass v (move c d) c') (hj : j ∈ Drift.arrivals v P w c' d)
    (hk : (UnitDiagonal.trueIdx (classPortWord v P w c' (fun i => decide (inDir w i = d))))[k]? =
      some (Drift.stableRank P w j)) :
    (UnitDiagonal.trueIdx (classPortWord v P w c (fun i => decide (outDir w i = d))))[k]? =
      some (Drift.stableRank P w (Drift.pred P j)) := by
  have hj' : j ∈ Drift.arrivals v P w (move c d) d := by
    rwa [Drift.arrivals_congr P w d ht]
  have hi := Drift.predecessor_mem h.1 hd hj'
  have hjP := (Drift.mem_arrivals.mp hj).1
  have hs := drift_succ_pred hjP
  obtain ⟨hiP, hic, hid⟩ := Drift.mem_departures.mp hi
  obtain ⟨_, hjc, hjd⟩ := Drift.mem_arrivals.mp hj
  rw [drift_outDir_eq] at hid
  rw [drift_inDir_eq] at hjd
  have hm := Drift.departure_rank_position_eq_arrival_rank_position_of_target h.1 hd hv ht hi
  rw [hs] at hm
  change (((Drift.classPhases v P w c).filter (fun i => decide (outDir w i = d))).filter _).length =
    (((Drift.classPhases v P w c').filter (fun i => decide (inDir w i = d))).filter _).length at hm
  rw [class_port_position hd hv (Drift.mem_classPhases.mpr ⟨hiP, hic⟩) _ (by simpa using hid),
    class_port_position hd hv (Drift.mem_classPhases.mpr ⟨hjP, hjc⟩) _ (by simpa using hjd),
    sorted_get_position (UnitDiagonal.pairwise_trueIdx _) hk] at hm
  rw [← hm]
  apply sorted_get_at_position (UnitDiagonal.pairwise_trueIdx _)
  apply UnitDiagonal.mem_trueIdx.mpr
  rw [classPortWord_at_phase hd hv (Drift.mem_classPhases.mpr ⟨hiP, hic⟩)]
  simpa using hid

private theorem path_succ {P len : Nat} (p : ContinuousPhasePath P len)
    {r : Nat} (hr : r < len) :
    p.phase (r + 1) = Drift.succ P (p.phase r) := by
  rcases p.successor hr with ⟨hs, _⟩ | ⟨he, hz, _⟩
  · rw [Drift.succ, UnitDiagonalMatching.succ, ← hs, Nat.mod_eq_of_lt (p.phase_lt _ (by omega))]
  · simp [Drift.succ, UnitDiagonalMatching.succ, he, hz]

private theorem walk_append_singleton (q : Point) (ds : List Direction) (d : Direction) :
    UnitDiagonal.walk q (ds ++ [d]) = move (UnitDiagonal.walk q ds) d := by
  induction ds generalizing q with
  | nil => rfl
  | cons a ds ih => simpa only [List.cons_append, UnitDiagonal.walk] using ih (move q a)

private theorem path_pos_eq_walk {P : Nat} {w : Nat → Bool} (ds : List Direction)
    (p : ContinuousPhasePath P ds.length)
    (hdirs : ∀ r (hr : r < ds.length), outDir w (p.phase r) = ds[r]) :
    ∀ r, r ≤ ds.length → p.pos w r = UnitDiagonal.walk (p.pos w 0) (ds.take r) := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
    have hrlt : r < ds.length := by omega
    rw [p.pos_step hrlt]
    change move (p.pos w r) (outDir w (p.phase r)) = _
    rw [ih (by omega), hdirs r hrlt, List.take_succ_eq_append_getElem hrlt, walk_append_singleton]

/-- General `ds.length`-step physical first return advances `stableRank` by `1` for any nonzero drift. -/
theorem walk_firstReturn_rank {v : Point} {P i₀ : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i₀ < P)
    (ds : List Direction) (hlen : 0 < ds.length)
    (hdirs : ∀ r (hr : r < ds.length),
      outDir w ((ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ ds.length).phase r) = ds[r])
    (hret : ∀ q, UnitDiagonal.FirstReturn q ds) :
    Drift.stableRank P w
        ((ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ ds.length).phase ds.length) =
      Drift.stableRank P w i₀ + 1 := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ ds.length
  have hp₀ : p.phase 0 = i₀ := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have hwalk := path_pos_eq_walk ds p hdirs
  obtain ⟨hclose, hfirst⟩ := (UnitDiagonal.firstReturn_iff _ _).mp (hret (p.pos w 0))
  have hend : p.pos w ds.length = p.pos w 0 := by
    rw [hwalk ds.length (Nat.le_refl _), List.take_length]
    exact hclose
  have hh := Drift.path_firstReturn_rank p hd hv hlen hend (by
    intro r hr0 hrlt
    rw [hwalk r (by omega)]
    exact hfirst r hr0 hrlt)
  simpa only [hp₀] using hh

theorem four_step_return_rank {v : Point} {P i₀ i₁ i₂ i₃ i₄ : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i₀ < P)
    (hs₀ : Drift.succ P i₀ = i₁) (hs₁ : Drift.succ P i₁ = i₂)
    (hs₂ : Drift.succ P i₂ = i₃) (hs₃ : Drift.succ P i₃ = i₄)
    (d₀ d₁ d₂ d₃ : Direction)
    (hd₀ : outDir w i₀ = d₀) (hd₁ : outDir w i₁ = d₁)
    (hd₂ : outDir w i₂ = d₂) (hd₃ : outDir w i₃ = d₃)
    (hret : ∀ q, UnitDiagonal.FirstReturn q [d₀, d₁, d₂, d₃]) :
    Drift.stableRank P w i₄ = Drift.stableRank P w i₀ + 1 := by
  let ds := [d₀, d₁, d₂, d₃]
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ ds.length
  have hp₀ : p.phase 0 = i₀ := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have hp₁ : p.phase 1 = i₁ := by rw [path_succ p (by simp [ds]), hp₀, hs₀]
  have hp₂ : p.phase 2 = i₂ := by rw [path_succ p (by simp [ds]), hp₁, hs₁]
  have hp₃ : p.phase 3 = i₃ := by rw [path_succ p (by simp [ds]), hp₂, hs₂]
  have hp₄ : p.phase 4 = i₄ := by rw [path_succ p (by simp [ds]), hp₃, hs₃]
  have hdirs : ∀ r (hr : r < ds.length), outDir w (p.phase r) = ds[r] := by
    intro r hr
    have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by simp [ds] at hr; omega
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa [ds, hp₀] using hd₀
    · simpa [ds, hp₁] using hd₁
    · simpa [ds, hp₂] using hd₂
    · simpa [ds, hp₃] using hd₃
  have hh := walk_firstReturn_rank hd hv hi ds (by simp [ds]) hdirs hret
  change Drift.stableRank P w (p.phase 4) = _ at hh
  rwa [hp₄] at hh

theorem eight_step_return_rank {v : Point} {P i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i₀ < P)
    (hs₀ : Drift.succ P i₀ = i₁) (hs₁ : Drift.succ P i₁ = i₂)
    (hs₂ : Drift.succ P i₂ = i₃) (hs₃ : Drift.succ P i₃ = i₄)
    (hs₄ : Drift.succ P i₄ = i₅) (hs₅ : Drift.succ P i₅ = i₆)
    (hs₆ : Drift.succ P i₆ = i₇) (hs₇ : Drift.succ P i₇ = i₈)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : Direction)
    (hd₀ : outDir w i₀ = d₀) (hd₁ : outDir w i₁ = d₁)
    (hd₂ : outDir w i₂ = d₂) (hd₃ : outDir w i₃ = d₃)
    (hd₄ : outDir w i₄ = d₄) (hd₅ : outDir w i₅ = d₅)
    (hd₆ : outDir w i₆ = d₆) (hd₇ : outDir w i₇ = d₇)
    (hret : ∀ q, UnitDiagonal.FirstReturn q [d₀, d₁, d₂, d₃, d₄, d₅, d₆, d₇]) :
    Drift.stableRank P w i₈ = Drift.stableRank P w i₀ + 1 := by
  let ds := [d₀, d₁, d₂, d₃, d₄, d₅, d₆, d₇]
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ ds.length
  have hp₀ : p.phase 0 = i₀ := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have hp₁ : p.phase 1 = i₁ := by rw [path_succ p (by simp [ds]), hp₀, hs₀]
  have hp₂ : p.phase 2 = i₂ := by rw [path_succ p (by simp [ds]), hp₁, hs₁]
  have hp₃ : p.phase 3 = i₃ := by rw [path_succ p (by simp [ds]), hp₂, hs₂]
  have hp₄ : p.phase 4 = i₄ := by rw [path_succ p (by simp [ds]), hp₃, hs₃]
  have hp₅ : p.phase 5 = i₅ := by rw [path_succ p (by simp [ds]), hp₄, hs₄]
  have hp₆ : p.phase 6 = i₆ := by rw [path_succ p (by simp [ds]), hp₅, hs₅]
  have hp₇ : p.phase 7 = i₇ := by rw [path_succ p (by simp [ds]), hp₆, hs₆]
  have hp₈ : p.phase 8 = i₈ := by rw [path_succ p (by simp [ds]), hp₇, hs₇]
  have hdirs : ∀ r (hr : r < ds.length), outDir w (p.phase r) = ds[r] := by
    intro r hr
    have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
      simp [ds] at hr; omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [ds, hp₀] using hd₀
    · simpa [ds, hp₁] using hd₁
    · simpa [ds, hp₂] using hd₂
    · simpa [ds, hp₃] using hd₃
    · simpa [ds, hp₄] using hd₄
    · simpa [ds, hp₅] using hd₅
    · simpa [ds, hp₆] using hd₆
    · simpa [ds, hp₇] using hd₇
  have hh := walk_firstReturn_rank hd hv hi ds (by simp [ds]) hdirs hret
  change Drift.stableRank P w (p.phase 8) = _ at hh
  rwa [hp₈] at hh

private theorem getElem_of_getElem? {α : Type} {l : List α} {k : Nat} {a : α}
    (hk : k < l.length) (h : l[k]? = some a) : l[k] = a :=
  Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans h)

private theorem countTrue_map_not (xs : List Bool) :
    UnitDiagonal.countTrue (xs.map (!·)) + UnitDiagonal.countTrue xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [UnitDiagonal.countTrue] <;> omega

theorem countTrue_classPortWord_dir_eq {v c c' : Point} {P : Nat} {w : Nat → Bool} {d : Direction}
    (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : Drift.SameClass v (move c d) c') :
    UnitDiagonal.countTrue (classPortWord v P w c (fun i => decide (outDir w i = d))) =
      UnitDiagonal.countTrue (classPortWord v P w c' (fun i => decide (inDir w i = d))) := by
  rw [classPortWord_count hd hv, classPortWord_count hd hv]
  change (Drift.departures v P w c d).length = (Drift.arrivals v P w c' d).length
  rw [← Drift.arrivals_congr P w d ht]
  exact Drift.departures_length_eq_arrivals_length h.1 hd

theorem class_succ_of_departure_port {v c c' : Point} {P r k : Nat} {w : Nat → Bool}
    {d : Direction} (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : Drift.SameClass v (move c d) c')
    (hr : r < (Drift.classPhases v P w c).length)
    (hdep : (UnitDiagonal.trueIdx (classPortWord v P w c (fun j => decide (outDir w j = d))))[k]? =
      some r) :
    let i := classPhaseAtRank v P w c r
    outDir w i = d ∧
    Drift.succ P i ∈ Drift.classPhases v P w c' ∧
    (UnitDiagonal.trueIdx (classPortWord v P w c' (fun j => decide (inDir w j = d))))[k]? =
      some (Drift.stableRank P w (Drift.succ P i)) := by
  intro i
  have him : i ∈ Drift.classPhases v P w c := classPhaseAtRank_mem hd hv hr
  have hir : Drift.stableRank P w i = r := classPhaseAtRank_rank hd hv hr
  have htrue : (classPortWord v P w c (fun j => decide (outDir w j = d)))[r]? = some true :=
    UnitDiagonal.mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨k, hdep⟩)
  have hget := classPortWord_getElem? (v := v) (P := P) (w := w) (c := c)
    (fun j => decide (outDir w j = d)) hr
  have hout : outDir w i = d := of_decide_eq_true (Option.some.inj (hget.symm.trans htrue))
  obtain ⟨hiP, hic⟩ := Drift.mem_classPhases.mp him
  have hid : i ∈ Drift.departures v P w c d := Drift.mem_departures.mpr ⟨hiP, hic, hout⟩
  have harr := (Drift.successor_mem_iff h.1 hd hiP).mpr hid
  rw [Drift.arrivals_congr P w d ht] at harr
  obtain ⟨hsP, hsc, _⟩ := Drift.mem_arrivals.mp harr
  have hidx := class_successor_port_index h hd hv ht hid (by rw [hir]; exact hdep)
  exact ⟨hout, Drift.mem_classPhases.mpr ⟨hsP, hsc⟩, hidx⟩

theorem class_succ_phaseAtRank_of_port_match {v c c' : Point} {P r s k : Nat} {w : Nat → Bool}
    {d : Direction} (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : Drift.SameClass v (move c d) c')
    (hr : r < (Drift.classPhases v P w c).length)
    (hs : s < (Drift.classPhases v P w c').length)
    (hdep : (UnitDiagonal.trueIdx (classPortWord v P w c (fun j => decide (outDir w j = d))))[k]? =
      some r)
    (harr : (UnitDiagonal.trueIdx (classPortWord v P w c' (fun j => decide (inDir w j = d))))[k]? =
      some s) :
    outDir w (classPhaseAtRank v P w c r) = d ∧
    Drift.succ P (classPhaseAtRank v P w c r) = classPhaseAtRank v P w c' s := by
  obtain ⟨hout, hmem, hidx⟩ := class_succ_of_departure_port h hd hv ht hr hdep
  have hrank : Drift.stableRank P w (Drift.succ P (classPhaseAtRank v P w c r)) = s :=
    Option.some.inj (hidx.symm.trans harr)
  exact ⟨hout, Drift.stableRank_injective_on_class hd hv hmem (classPhaseAtRank_mem hd hv hs)
    (hrank.trans (classPhaseAtRank_rank hd hv hs).symm)⟩

theorem class_pred_of_arrival_port {v c c' : Point} {P r k : Nat} {w : Nat → Bool}
    {d : Direction} (h : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (ht : Drift.SameClass v (move c d) c')
    (hr : r < (Drift.classPhases v P w c').length)
    (harr : (UnitDiagonal.trueIdx (classPortWord v P w c' (fun j => decide (inDir w j = d))))[k]? =
      some r) :
    let j := classPhaseAtRank v P w c' r
    let i := Drift.pred P j
    i ∈ Drift.classPhases v P w c ∧
    Drift.succ P i = j ∧
    outDir w i = d ∧
    (UnitDiagonal.trueIdx (classPortWord v P w c (fun j => decide (outDir w j = d))))[k]? =
      some (Drift.stableRank P w i) := by
  intro j i
  have hjm : j ∈ Drift.classPhases v P w c' := classPhaseAtRank_mem hd hv hr
  have hjr : Drift.stableRank P w j = r := classPhaseAtRank_rank hd hv hr
  have htrue : (classPortWord v P w c' (fun m => decide (inDir w m = d)))[r]? = some true :=
    UnitDiagonal.mem_trueIdx.mp (List.mem_iff_getElem?.mpr ⟨k, harr⟩)
  have hget := classPortWord_getElem? (v := v) (P := P) (w := w) (c := c')
    (fun m => decide (inDir w m = d)) hr
  have hin : inDir w j = d := of_decide_eq_true (Option.some.inj (hget.symm.trans htrue))
  obtain ⟨hjP, hjc⟩ := Drift.mem_classPhases.mp hjm
  have hja : j ∈ Drift.arrivals v P w c' d := Drift.mem_arrivals.mpr ⟨hjP, hjc, hin⟩
  have hja' : j ∈ Drift.arrivals v P w (move c d) d := by rwa [Drift.arrivals_congr P w d ht]
  have hdep := Drift.predecessor_mem h.1 hd hja'
  obtain ⟨hiP, hic, hout⟩ := Drift.mem_departures.mp hdep
  rw [drift_outDir_eq] at hout
  have hidx := class_predecessor_port_index h hd hv ht hja (by rw [hjr]; exact harr)
  exact ⟨Drift.mem_classPhases.mpr ⟨hiP, hic⟩, drift_succ_pred hjP, hout, hidx⟩

/-! ## 4. Target (1): Adjacent-lane first-return relation on the first and second inner layers -/

/-- First-inner-layer word `100` (early type). -/
def word100 : List Bool := [true, false, false]
/-- First-inner-layer word `1000` (early type). -/
def word1000 : List Bool := [true, false, false, false]
/-- First-inner-layer word `001` (late type). -/
def word001 : List Bool := [false, false, true]
/-- First-inner-layer word `0010` (late type). -/
def word0010 : List Bool := [false, false, true, false]

/-- The four valid nonempty first-inner-layer arrival words with one upper arrival and one upper departure. -/
def IsFirstInnerWord (a : List Bool) : Prop :=
  a = word100 ∨ a = word1000 ∨ a = word001 ∨ a = word0010

/-- Second-inner-layer upper-arrival rank-list index `i(b)`: `0` for early (`100`/`1000`), `1` for late (`001`/`0010`). -/
def arrPortIdx (b : List Bool) : Nat :=
  if b.headD false then 0 else 1

/-- Second-inner-layer upper-departure rank-list index `j(a)`: `1` for early (`100`/`1000`), `0` for late (`001`/`0010`). -/
def depPortIdx (a : List Bool) : Nat :=
  if a.headD false then 1 else 0

theorem laneBeta_eq {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (n : Nat) (r : Int) :
    laneBeta m P w (topLayer P w - (n : Int)) r =
      UnitDiagonal.beta (laneAlpha m P w (topLayer P w - (n : Int)) r) (decide (n % 2 = 1)) := by
  have hb := classBetaWord_eq (c := laneCell (topLayer P w - (n : Int)) r)
    h hd (diagDrift_ne_zero hm) (layer_diagDrift m)
  rw [layer_laneCell] at hb
  have he : topLayer P w - (topLayer P w - (n : Int)) = (n : Int) := by omega
  have hmod : ((n : Int) % 2 = 1) ↔ n % 2 = 1 := by omega
  simpa only [laneBeta, laneAlpha, he, decide_eq_decide.mpr hmod] using hb

theorem lane_incoming_portWord {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (n : Nat) (r : Int) (b : Bool) :
    classPortWord (diagDrift m) P w (laneCell (topLayer P w - (n : Int)) r)
        (fun i => decide (inDir w i = enterDir n b)) =
      if b then laneAlpha m P w (topLayer P w - (n : Int)) r
      else (laneAlpha m P w (topLayer P w - (n : Int)) r).map (!·) :=
  incoming_classPortWord h hd (diagDrift_ne_zero hm) (layer_diagDrift m) n (layer_laneCell _ _) b

theorem lane_outgoing_portWord {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (n : Nat) (r : Int) (b : Bool) :
    classPortWord (diagDrift m) P w (laneCell (topLayer P w - (n : Int)) r)
        (fun i => decide (outDir w i = leaveDir n b)) =
      if b then laneBeta m P w (topLayer P w - (n : Int)) r
      else (laneBeta m P w (topLayer P w - (n : Int)) r).map (!·) :=
  outgoing_classPortWord h hd (diagDrift_ne_zero hm) (layer_diagDrift m) n (layer_laneCell _ _) b

theorem laneBeta_depth1 {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int) :
    laneBeta m P w (topLayer P w - 1) r =
      UnitDiagonal.beta (laneAlpha m P w (topLayer P w - 1) r) true :=
  laneBeta_eq h hm hd 1 r

theorem laneBeta_depth2 {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int) :
    laneBeta m P w (topLayer P w - 2) r =
      UnitDiagonal.beta (laneAlpha m P w (topLayer P w - 2) r) false :=
  laneBeta_eq h hm hd 2 r

theorem laneBeta_depth3 {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int) :
    laneBeta m P w (topLayer P w - 3) r =
      UnitDiagonal.beta (laneAlpha m P w (topLayer P w - 3) r) true :=
  laneBeta_eq h hm hd 3 r

/-- If top-layer classes at lanes `r` and `r + 1` are both visited, then the first-inner-layer
lane `r` has arrival word in `{100, 1000, 001, 0010}`. -/
theorem firstInner_of_top_occupied {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    (hT0 : (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w) r)).length ≠ 0)
    (hT1 : (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w) (r + 1))).length ≠ 0) :
    IsFirstInnerWord (laneAlpha m P w (topLayer P w - 1) r) := by
  have hv := diagDrift_ne_zero hm
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_diagDrift m
  have hT_props (s : Int)
      (hne : (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w) s)).length ≠ 0) :
      UnitDiagonal.countTrue (classPortWord (diagDrift m) P w (laneCell (topLayer P w) s)
          (fun i => decide (inDir w i = .east))) = 1 ∧
      UnitDiagonal.countTrue (classPortWord (diagDrift m) P w (laneCell (topLayer P w) s)
          (fun i => decide (outDir w i = .south))) = 1 := by
    have hle := TwoCellDiagonal.topLayer_class_length_le_one_of_layer_zero h hlv
      (c := laneCell (topLayer P w) s) (layer_laneCell _ _)
    rw [hd] at hle
    have hlen1 : (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w) s)).length = 1 := by
      omega
    have hmem := classPhaseAtRank_mem hd hv (show 0 < (Drift.classPhases (diagDrift m) P w
      (laneCell (topLayer P w) s)).length by omega)
    obtain ⟨hiP, hisc⟩ := Drift.mem_classPhases.mp hmem
    have hitop : layer (wordPos w (classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w) s) 0)) =
        topLayer P w :=
      (TwoCellDiagonal.layer_eq_of_sameClass (layer_diagDrift m) hisc).trans (layer_laneCell _ _)
    have hrig := TwoCellDiagonal.topLayer_phase_rigid_of_layer_zero h hlv hiP hitop
    have hcr : classRankedPhases (diagDrift m) P w (laneCell (topLayer P w) s) =
        [classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w) s) 0] := by
      simp [classRankedPhases, hlen1]
    simp only [classPortWord, hcr, List.map_cons, List.map_nil, hrig.2.2.1, hrig.2.2.2.1,
      decide_true, UnitDiagonal.countTrue]
    exact ⟨rfl, rfl⟩
  have hI : UnitDiagonal.countTrue (laneAlpha m P w (topLayer P w - 1) r) = 1 := by
    have hin : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) r)
        (fun i => decide (inDir w i = .south)) = laneAlpha m P w (topLayer P w - 1) r :=
      lane_incoming_portWord h hm hd 1 r true
    rw [← hin, ← countTrue_classPortWord_dir_eq (c := laneCell (topLayer P w) r) h hd hv
      (by rw [move_laneCell_south]; exact Drift.SameClass.refl _ _)]
    exact (hT_props r hT0).2
  have hJ : UnitDiagonal.countTrue (UnitDiagonal.beta (laneAlpha m P w (topLayer P w - 1) r) true) = 1 := by
    have hout : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) r)
        (fun i => decide (outDir w i = .east)) = laneBeta m P w (topLayer P w - 1) r :=
      lane_outgoing_portWord h hm hd 1 r true
    rw [← laneBeta_depth1 h hm hd r, ← hout,
      countTrue_classPortWord_dir_eq (c' := laneCell (topLayer P w) (r + 1)) h hd hv
        (by rw [move_laneCell_east]; rw [show topLayer P w - 1 + 1 = topLayer P w by omega]; exact Drift.SameClass.refl _ _)]
    exact (hT_props (r + 1) hT1).1
  have hne : laneAlpha m P w (topLayer P w - 1) r ≠ [] := by
    intro hnil; rw [hnil] at hI; simp [UnitDiagonal.countTrue] at hI
  exact UnitDiagonal.odd_layer_single_true _ hI hJ hne

/-- **Target (1): Adjacent-lane first-return relation on the first and second inner layers.**
For every `m > 0`, `ConsistentWord P w` with full drift `(m, -m)`, and lane `r`, if the adjacent
first-inner-layer arrival words `a = α(T - 1, r)` and `b = α(T - 1, r + 1)` lie in
`{100, 1000, 001, 0010}`, then the upper arrival/departure rank lists
`p = trueIdx (α(T - 2, r))` and `q = trueIdx (β(T - 2, r))` on the second inner layer satisfy
`p.length = b.length - 1`, `q.length = a.length - 1`, and `p[arrPortIdx b] = q[depPortIdx a] + 1`
(early `100`/`1000`: `i = 0, j = 1`; late `001`/`0010`: `i = 1, j = 0`).
No minimality or global top-layer occupancy is assumed. -/
theorem adjacent_lane_second_inner_relation {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    {a b : List Bool}
    (ha : laneAlpha m P w (topLayer P w - 1) r = a)
    (hb : laneAlpha m P w (topLayer P w - 1) (r + 1) = b)
    (haW : IsFirstInnerWord a) (hbW : IsFirstInnerWord b) :
    let p := UnitDiagonal.trueIdx (laneAlpha m P w (topLayer P w - 2) r)
    let q := UnitDiagonal.trueIdx (laneBeta m P w (topLayer P w - 2) r)
    p.length = b.length - 1 ∧
    q.length = a.length - 1 ∧
    ∃ pv qv, p[arrPortIdx b]? = some pv ∧ q[depPortIdx a]? = some qv ∧ pv = qv + 1 := by
  intro p q
  have hv := diagDrift_ne_zero hm
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_diagDrift m
  let T := topLayer P w
  let Ar := laneCell (T - 1) r
  let Ar1 := laneCell (T - 1) (r + 1)
  let Br := laneCell (T - 2) r
  let Tr1 := laneCell T (r + 1)
  have hβAr : laneBeta m P w (T - 1) r = UnitDiagonal.beta a true := by
    rw [laneBeta_depth1 h hm hd r, ha]
  have hβAr1 : laneBeta m P w (T - 1) (r + 1) = UnitDiagonal.beta b true := by
    rw [laneBeta_depth1 h hm hd (r + 1), hb]
  have hNA : classPortWord (diagDrift m) P w Ar (fun i => decide (inDir w i = .north)) =
      a.map (!·) := by
    have h1 : classPortWord (diagDrift m) P w Ar (fun i => decide (inDir w i = .north)) =
        (laneAlpha m P w (T - 1) r).map (!·) := lane_incoming_portWord h hm hd 1 r false
    rwa [ha] at h1
  have hWA1 : classPortWord (diagDrift m) P w Ar1 (fun i => decide (outDir w i = .west)) =
      (UnitDiagonal.beta b true).map (!·) := by
    have h1 : classPortWord (diagDrift m) P w Ar1 (fun i => decide (outDir w i = .west)) =
        (laneBeta m P w (T - 1) (r + 1)).map (!·) := lane_outgoing_portWord h hm hd 1 (r + 1) false
    rwa [hβAr1] at h1
  have hWB : classPortWord (diagDrift m) P w Br (fun i => decide (inDir w i = .west)) =
      laneAlpha m P w (T - 2) r := lane_incoming_portWord h hm hd 2 r true
  have hNB : classPortWord (diagDrift m) P w Br (fun i => decide (outDir w i = .north)) =
      laneBeta m P w (T - 2) r := lane_outgoing_portWord h hm hd 2 r true
  have hmBA : Drift.SameClass (diagDrift m) (move Br .north) Ar := by
    rw [move_laneCell_north]
    have : T - 2 + 1 = T - 1 := by omega
    rw [this]; exact Drift.SameClass.refl _ _
  have hmAB : Drift.SameClass (diagDrift m) (move Ar1 .west) Br := by
    rw [move_laneCell_west]
    have h1 : T - 1 - 1 = T - 2 := by omega
    have h2 : r + 1 - 1 = r := by omega
    rw [h1, h2]; exact Drift.SameClass.refl _ _
  have hmAT : Drift.SameClass (diagDrift m) (move Ar .east) Tr1 := by
    rw [move_laneCell_east]
    have : T - 1 + 1 = T := by omega
    rw [this]; exact Drift.SameClass.refl _ _
  have hmTA : Drift.SameClass (diagDrift m) (move Tr1 .south) Ar1 := by
    rw [move_laneCell_south]; exact Drift.SameClass.refl _ _
  -- Lengths of `p` and `q`
  have hplen : p.length = b.length - 1 := by
    change (UnitDiagonal.trueIdx (laneAlpha m P w (T - 2) r)).length = b.length - 1
    rw [UnitDiagonal.trueIdx_length, ← hWB,
      ← countTrue_classPortWord_dir_eq h hd hv hmAB, hWA1]
    rcases hbW with rfl | rfl | rfl | rfl <;> rfl
  have hqlen : q.length = a.length - 1 := by
    change (UnitDiagonal.trueIdx (laneBeta m P w (T - 2) r)).length = a.length - 1
    rw [UnitDiagonal.trueIdx_length, ← hNB,
      countTrue_classPortWord_dir_eq h hd hv hmBA, hNA]
    rcases haW with rfl | rfl | rfl | rfl <;> rfl
  -- Unique east-departure rank `k_out` on `A_r` and south-arrival rank `k_in` on `A_{r+1}`
  let k_out : Nat := if a.headD false then 2 else 0
  let k_in : Nat := if b.headD false then 0 else 2
  have hk_out_lt : k_out < (Drift.classPhases (diagDrift m) P w Ar).length := by
    have hl : a.length = (Drift.classPhases (diagDrift m) P w Ar).length := by
      rw [← ha]; exact classPortWord_length _ _ _ _ _
    rw [← hl]
    rcases haW with rfl | rfl | rfl | rfl <;> decide
  have hk_in_lt : k_in < (Drift.classPhases (diagDrift m) P w Ar1).length := by
    have hl : b.length = (Drift.classPhases (diagDrift m) P w Ar1).length := by
      rw [← hb]; exact classPortWord_length _ _ _ _ _
    rw [← hl]
    rcases hbW with rfl | rfl | rfl | rfl <;> decide
  -- Step 1: `b_dep --N--> a_out` (index `depPortIdx a` in `q`)
  have hNA_idx : (UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w Ar
      (fun i => decide (inDir w i = .north))))[depPortIdx a]? = some k_out := by
    rw [hNA]
    rcases haW with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨hb_dep_mem, hb_dep_succ, hbo, hq_idx⟩ :=
    class_pred_of_arrival_port h hd hv hmBA hk_out_lt hNA_idx
  rw [hNB] at hq_idx
  let a_out := classPhaseAtRank (diagDrift m) P w Ar k_out
  let b_dep := Drift.pred P a_out
  -- Step 2: `a_out --E--> t` (landing on top layer `T_{r+1}`)
  have hoa_out : outDir w a_out = .east := by
    have hbm := classBetaWord_at_phase hd hv (classPhaseAtRank_mem hd hv hk_out_lt)
    rw [classPhaseAtRank_rank hd hv hk_out_lt] at hbm
    change (laneBeta m P w (T - 1) r)[k_out]? = some (LangtonsAnt.beta w a_out) at hbm
    rw [hβAr] at hbm
    have hbt : (UnitDiagonal.beta a true)[k_out]? = some true := by
      rcases haW with rfl | rfl | rfl | rfl <;> rfl
    have hbeta_t : LangtonsAnt.beta w a_out = true := Option.some.inj (hbm.symm.trans hbt)
    have hlay : layer (wordPos w a_out) = T - 1 :=
      (TwoCellDiagonal.layer_eq_of_sameClass (layer_diagDrift m)
        (Drift.mem_classPhases.mp (classPhaseAtRank_mem hd hv hk_out_lt)).2).trans
        (layer_laneCell _ _)
    have hdep : depth P w a_out % 2 = 1 := by unfold depth; omega
    have ho := outDir_eq_of_depth_beta_of_layer_zero h hlv a_out
    have hne0 : depth P w a_out % 2 ≠ 0 := by omega
    simp [hne0, hbeta_t] at ho
    exact ho
  let t := Drift.succ P a_out
  have ha_out_dep : a_out ∈ Drift.departures (diagDrift m) P w Ar .east := by
    obtain ⟨hp, hsc⟩ := Drift.mem_classPhases.mp (classPhaseAtRank_mem hd hv hk_out_lt)
    exact Drift.mem_departures.mpr ⟨hp, hsc, hoa_out⟩
  have ht_arr : t ∈ Drift.arrivals (diagDrift m) P w Tr1 .east := by
    have h1 := (Drift.successor_mem_iff h.1 hd (Drift.mem_departures.mp ha_out_dep).1).mpr ha_out_dep
    rwa [Drift.arrivals_congr P w .east hmAT] at h1
  obtain ⟨htP, htsc, _⟩ := Drift.mem_arrivals.mp ht_arr
  have httop : layer (wordPos w t) = topLayer P w :=
    (TwoCellDiagonal.layer_eq_of_sameClass (layer_diagDrift m) htsc).trans (layer_laneCell _ _)
  have hot : outDir w t = .south :=
    (TwoCellDiagonal.topLayer_phase_rigid_of_layer_zero h hlv htP httop).2.2.2.1
  -- Step 3: `t --S--> a_in` (unique south-arriving phase of `A_{r+1}`)
  let a_in := Drift.succ P t
  have ht_dep : t ∈ Drift.departures (diagDrift m) P w Tr1 .south :=
    Drift.mem_departures.mpr ⟨htP, htsc, hot⟩
  have ha_in_arr : a_in ∈ Drift.arrivals (diagDrift m) P w Ar1 .south := by
    have h1 := (Drift.successor_mem_iff h.1 hd htP).mpr ht_dep
    rwa [Drift.arrivals_congr P w .south hmTA] at h1
  obtain ⟨ha_inP, ha_insc, ha_in_dir⟩ := Drift.mem_arrivals.mp ha_in_arr
  rw [drift_inDir_eq] at ha_in_dir
  have ha_in_mem : a_in ∈ Drift.classPhases (diagDrift m) P w Ar1 :=
    Drift.mem_classPhases.mpr ⟨ha_inP, ha_insc⟩
  have ha_in_rank : Drift.stableRank P w a_in = k_in := by
    have ham := classAlphaWord_at_phase hd hv ha_in_mem
    have hαt : LangtonsAnt.alpha w a_in = true := by simp [LangtonsAnt.alpha, ha_in_dir]
    rw [hαt] at ham
    change (laneAlpha m P w (T - 1) (r + 1))[Drift.stableRank P w a_in]? = some true at ham
    rw [hb] at ham
    have hmem := UnitDiagonal.mem_trueIdx.mpr ham
    rcases hbW with rfl | rfl | rfl | rfl <;>
      simpa [k_in, word100, word1000, word001, word0010, UnitDiagonal.trueIdx] using hmem
  have ha_in_eq : a_in = classPhaseAtRank (diagDrift m) P w Ar1 k_in := by
    rw [← ha_in_rank]
    exact (classPhaseAtRank_eq hd hv ha_in_mem).symm
  -- Step 4: `a_in --W--> b_arr` (index `arrPortIdx b` in `p`)
  have hWA1_idx : (UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w Ar1
      (fun i => decide (outDir w i = .west))))[arrPortIdx b]? = some k_in := by
    rw [hWA1]
    rcases hbW with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨hoa_in', _, hp_idx⟩ := class_succ_of_departure_port h hd hv hmAB hk_in_lt hWA1_idx
  rw [hWB, ← ha_in_eq] at hp_idx
  have hoa_in : outDir w a_in = .west := by rwa [ha_in_eq]
  -- Four-step `NESW` physical first return on `B_r`
  have hret := four_step_return_rank hd hv (Drift.mem_classPhases.mp hb_dep_mem).1
    hb_dep_succ rfl rfl rfl .north .east .south .west hbo hoa_out hot hoa_in
    UnitDiagonal.firstReturn_NESW
  exact ⟨hplen, hqlen, _, _, hp_idx, hq_idx, hret⟩

/-- Direct indexed form of Target (1): `p[arrPortIdx b] = q[depPortIdx a] + 1`. -/
theorem adjacent_lane_second_inner_getElem {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    {a b : List Bool}
    (ha : laneAlpha m P w (topLayer P w - 1) r = a)
    (hb : laneAlpha m P w (topLayer P w - 1) (r + 1) = b)
    (haW : IsFirstInnerWord a) (hbW : IsFirstInnerWord b) :
    let p := UnitDiagonal.trueIdx (laneAlpha m P w (topLayer P w - 2) r)
    let q := UnitDiagonal.trueIdx (laneBeta m P w (topLayer P w - 2) r)
    ∃ (hp : arrPortIdx b < p.length) (hq : depPortIdx a < q.length),
      p[arrPortIdx b]'hp = q[depPortIdx a]'hq + 1 := by
  intro p q
  obtain ⟨_, _, pv, qv, hp?, hq?, heq⟩ :=
    adjacent_lane_second_inner_relation h hm hd r ha hb haW hbW
  have hp : arrPortIdx b < p.length := UnitDiagonal.lt_length_of_getElem? hp?
  have hq : depPortIdx a < q.length := UnitDiagonal.lt_length_of_getElem? hq?
  refine ⟨hp, hq, ?_⟩
  rw [getElem_of_getElem? hp hp?, getElem_of_getElem? hq hq?]
  exact heq

/-- Purely combinatorial lower bound on an even-depth port word: `p[0] = q[1] + 1` forces
at least three entries in `q = trueIdx (beta α false)`. -/
theorem even_q_len_ge_three_of_p0_eq_q1_succ (α : List Bool) {a b : Nat}
    (hp0 : (UnitDiagonal.trueIdx α)[0]? = some a)
    (hq1 : (UnitDiagonal.trueIdx (UnitDiagonal.beta α false))[1]? = some b)
    (hab : a = b + 1) :
    3 ≤ (UnitDiagonal.trueIdx (UnitDiagonal.beta α false)).length := by
  have hpair_p := UnitDiagonal.pairwise_trueIdx α
  have hpair_q := UnitDiagonal.pairwise_trueIdx (UnitDiagonal.beta α false)
  have hq_len2 : 1 < (UnitDiagonal.trueIdx (UnitDiagonal.beta α false)).length :=
    UnitDiagonal.lt_length_of_getElem? hq1
  have hpa : a ∈ UnitDiagonal.trueIdx α := List.mem_iff_getElem?.mpr ⟨0, hp0⟩
  have ha_true : α[a]? = some true := UnitDiagonal.mem_trueIdx.mp hpa
  have han : a < α.length := UnitDiagonal.lt_length_of_getElem? ha_true
  have hbelow : ∀ k, k < a → α[k]? = some false := by
    intro k hk
    have hklen : k < α.length := by omega
    have hknot : k ∉ UnitDiagonal.trueIdx α := fun hm =>
      by have := UnitDiagonal.le_of_pairwise_zero hpair_p hp0 hm; omega
    have hkem : α[k]? = some α[k] := List.getElem?_eq_getElem hklen
    rw [hkem]
    cases hv : α[k]
    · rfl
    · exact absurd (UnitDiagonal.mem_trueIdx.mpr (by rw [hkem, hv])) hknot
  have hqiff : ∀ k, k < a → (k ∈ UnitDiagonal.trueIdx (UnitDiagonal.beta α false) ↔ k % 2 = 1) := by
    intro k hk
    rw [UnitDiagonal.mem_trueIdx, UnitDiagonal.beta_false_of_alpha_false (hbelow k hk)]
    simp
  have hqb : b ∈ UnitDiagonal.trueIdx (UnitDiagonal.beta α false) := List.mem_iff_getElem?.mpr ⟨1, hq1⟩
  have hbodd : b % 2 = 1 := (hqiff b (by omega)).mp hqb
  have haeven : a % 2 = 0 := by omega
  have ha_ne2 : a ≠ 2 := by
    intro h2
    have hq0 : (UnitDiagonal.trueIdx (UnitDiagonal.beta α false))[0]? =
        some (UnitDiagonal.trueIdx (UnitDiagonal.beta α false))[0] :=
      List.getElem?_eq_getElem (by omega)
    have hlt := UnitDiagonal.lt_of_pairwise hpair_q (by omega : 0 < 1) hq0 hq1
    have h0z : (UnitDiagonal.trueIdx (UnitDiagonal.beta α false))[0] = 0 := by omega
    have hmem0 : (0 : Nat) ∈ UnitDiagonal.trueIdx (UnitDiagonal.beta α false) := by
      rw [List.mem_iff_getElem?]; exact ⟨0, by rw [hq0, h0z]⟩
    have := (hqiff 0 (by omega)).mp hmem0
    omega
  have ha_ge4 : 4 ≤ a := by omega
  have ha_q : a ∈ UnitDiagonal.trueIdx (UnitDiagonal.beta α false) :=
    UnitDiagonal.mem_trueIdx.mpr (UnitDiagonal.beta_true_of_alpha_true_even ha_true haeven)
  have hsub : ∀ k, k ∈ ([1, 3, a] : List Nat) →
      k ∈ UnitDiagonal.trueIdx (UnitDiagonal.beta α false) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact (hqiff 1 (by omega)).mpr rfl
    · exact (hqiff 3 (by omega)).mpr rfl
    · exact ha_q
  have hnd : ([1, 3, a] : List Nat).Nodup := by simp [List.nodup_cons]; omega
  simpa using UnitDiagonal.length_le_of_forall_mem [1, 3, a] hnd hsub

/-- Corollary of Target (1) (Round 1 / Round 9): the adjacent first-inner-layer patterns
`(100, 100)` and `(100, 1000)` are impossible, without assuming global top occupancy. -/
theorem no_adjacent_100_early {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    (ha : laneAlpha m P w (topLayer P w - 1) r = word100)
    (hb : laneAlpha m P w (topLayer P w - 1) (r + 1) = word100 ∨
          laneAlpha m P w (topLayer P w - 1) (r + 1) = word1000) : False := by
  have hβB := laneBeta_depth2 h hm hd r
  rcases hb with hb | hb
  · obtain ⟨_, hqlen, pv, qv, hp0, hq1, heq⟩ :=
      adjacent_lane_second_inner_relation h hm hd r ha hb (Or.inl rfl) (Or.inl rfl)
    rw [hβB] at hqlen hq1
    have hge := even_q_len_ge_three_of_p0_eq_q1_succ _ hp0 hq1 heq
    simp [word100] at hqlen
    omega
  · obtain ⟨_, hqlen, pv, qv, hp0, hq1, heq⟩ :=
      adjacent_lane_second_inner_relation h hm hd r ha hb (Or.inl rfl) (Or.inr (Or.inl rfl))
    rw [hβB] at hqlen hq1
    have hge := even_q_len_ge_three_of_p0_eq_q1_succ _ hp0 hq1 heq
    simp [word100] at hqlen
    omega

/-- Corollary of Target (1): adjacent `1000, 1000` lanes on the first inner layer force
`W8` or `W9` on the corresponding second-inner-layer lane. -/
theorem second_inner_W8_or_W9_of_adjacent_1000 {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    (ha : laneAlpha m P w (topLayer P w - 1) r = word1000)
    (hb : laneAlpha m P w (topLayer P w - 1) (r + 1) = word1000) :
    laneAlpha m P w (topLayer P w - 2) r = UnitDiagonal.W8 ∨
      laneAlpha m P w (topLayer P w - 2) r = UnitDiagonal.W9 := by
  obtain ⟨hplen, hqlen, pv, qv, hp0, hq1, heq⟩ :=
    adjacent_lane_second_inner_relation h hm hd r ha hb
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  have hβB := laneBeta_depth2 h hm hd r
  rw [hβB] at hqlen hq1
  simp only [word1000, List.length_cons, List.length_nil] at hplen hqlen
  exact (UnitDiagonal.even_two_or_three _ 3 pv qv hplen hqlen (Or.inr rfl)
    (by omega) (by omega) hp0 hq1 heq).2

/-! ## 5. Target (2): No three consecutive `1000` lanes on the first inner layer -/

private theorem firstInner_1000_ports {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (s : Int)
    (hA : laneAlpha m P w (topLayer P w - 1) s = word1000) :
    (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 1) s)).length = 4 ∧
    UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) s)
      (fun i => decide (inDir w i = .north))) = [1, 2, 3] ∧
    UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) s)
      (fun i => decide (outDir w i = .west))) = [0, 1, 3] := by
  have hlen : (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 1) s)).length = 4 := by
    have hl := classPortWord_length (diagDrift m) P w (laneCell (topLayer P w - 1) s)
      (LangtonsAnt.alpha w)
    change (laneAlpha m P w (topLayer P w - 1) s).length = _ at hl
    rw [hA] at hl
    simpa [word1000] using hl.symm
  have hNA : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) s)
      (fun i => decide (inDir w i = .north)) = word1000.map (!·) := by
    have h1 : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) s)
        (fun i => decide (inDir w i = .north)) =
        (laneAlpha m P w (topLayer P w - 1) s).map (!·) :=
      lane_incoming_portWord h hm hd 1 s false
    rwa [hA] at h1
  have hWA : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) s)
      (fun i => decide (outDir w i = .west)) = (UnitDiagonal.beta word1000 true).map (!·) := by
    have h1 : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) s)
        (fun i => decide (outDir w i = .west)) =
        (laneBeta m P w (topLayer P w - 1) s).map (!·) :=
      lane_outgoing_portWord h hm hd 1 s false
    rw [laneBeta_depth1 h hm hd s, hA] at h1
    exact h1
  refine ⟨hlen, ?_, ?_⟩
  · rw [hNA]; decide
  · rw [hWA]; decide

private theorem adjacent_1000_top_bridge {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (s : Int)
    (hA0 : laneAlpha m P w (topLayer P w - 1) s = word1000)
    (hA1 : laneAlpha m P w (topLayer P w - 1) (s + 1) = word1000) :
    let a₂ := classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 1) s) 2
    let a₀ := classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 1) (s + 1)) 0
    ∃ t,
      Drift.succ P a₂ = t ∧ outDir w a₂ = .east ∧
      Drift.succ P t = a₀ ∧ outDir w t = .south := by
  intro a₂ a₀
  have hv := diagDrift_ne_zero hm
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_diagDrift m
  have hlen0 := (firstInner_1000_ports h hm hd s hA0).1
  have hlen1 := (firstInner_1000_ports h hm hd (s + 1) hA1).1
  have ha₂m : a₂ ∈ Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 1) s) :=
    classPhaseAtRank_mem hd hv (by omega)
  have hoa₂ : outDir w a₂ = .east := by
    have hbm := classBetaWord_at_phase hd hv ha₂m
    rw [classPhaseAtRank_rank hd hv (by omega)] at hbm
    change (laneBeta m P w (topLayer P w - 1) s)[2]? = some (LangtonsAnt.beta w a₂) at hbm
    rw [laneBeta_depth1 h hm hd s, hA0] at hbm
    have hbeta_t : LangtonsAnt.beta w a₂ = true := Option.some.inj hbm.symm
    have hlay : layer (wordPos w a₂) = topLayer P w - 1 :=
      (TwoCellDiagonal.layer_eq_of_sameClass (layer_diagDrift m)
        (Drift.mem_classPhases.mp ha₂m).2).trans (layer_laneCell _ _)
    have hne0 : depth P w a₂ % 2 ≠ 0 := by unfold depth; omega
    have ho := outDir_eq_of_depth_beta_of_layer_zero h hlv a₂
    simp [hne0, hbeta_t] at ho
    exact ho
  let t := Drift.succ P a₂
  have hmAT : Drift.SameClass (diagDrift m)
      (move (laneCell (topLayer P w - 1) s) .east) (laneCell (topLayer P w) (s + 1)) := by
    rw [move_laneCell_east, show topLayer P w - 1 + 1 = topLayer P w by omega]
    exact Drift.SameClass.refl _ _
  have hmTA : Drift.SameClass (diagDrift m)
      (move (laneCell (topLayer P w) (s + 1)) .south) (laneCell (topLayer P w - 1) (s + 1)) := by
    rw [move_laneCell_south]; exact Drift.SameClass.refl _ _
  obtain ⟨ha₂P, ha₂sc⟩ := Drift.mem_classPhases.mp ha₂m
  have ha₂dep : a₂ ∈ Drift.departures (diagDrift m) P w (laneCell (topLayer P w - 1) s) .east :=
    Drift.mem_departures.mpr ⟨ha₂P, ha₂sc, hoa₂⟩
  have ht_arr : t ∈ Drift.arrivals (diagDrift m) P w (laneCell (topLayer P w) (s + 1)) .east := by
    have h1 := (Drift.successor_mem_iff h.1 hd ha₂P).mpr ha₂dep
    rwa [Drift.arrivals_congr P w .east hmAT] at h1
  obtain ⟨htP, htsc, _⟩ := Drift.mem_arrivals.mp ht_arr
  have httop : layer (wordPos w t) = topLayer P w :=
    (TwoCellDiagonal.layer_eq_of_sameClass (layer_diagDrift m) htsc).trans (layer_laneCell _ _)
  have hot : outDir w t = .south :=
    (TwoCellDiagonal.topLayer_phase_rigid_of_layer_zero h hlv htP httop).2.2.2.1
  have ht_dep : t ∈ Drift.departures (diagDrift m) P w (laneCell (topLayer P w) (s + 1)) .south :=
    Drift.mem_departures.mpr ⟨htP, htsc, hot⟩
  have ha₀_arr : Drift.succ P t ∈
      Drift.arrivals (diagDrift m) P w (laneCell (topLayer P w - 1) (s + 1)) .south := by
    have h1 := (Drift.successor_mem_iff h.1 hd htP).mpr ht_dep
    rwa [Drift.arrivals_congr P w .south hmTA] at h1
  obtain ⟨ha₀P, ha₀sc, ha₀dir⟩ := Drift.mem_arrivals.mp ha₀_arr
  rw [drift_inDir_eq] at ha₀dir
  have ha₀m : Drift.succ P t ∈ Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 1) (s + 1)) :=
    Drift.mem_classPhases.mpr ⟨ha₀P, ha₀sc⟩
  have ha₀r : Drift.stableRank P w (Drift.succ P t) = 0 := by
    have ham := classAlphaWord_at_phase hd hv ha₀m
    have hαt : LangtonsAnt.alpha w (Drift.succ P t) = true := by simp [LangtonsAnt.alpha, ha₀dir]
    rw [hαt] at ham
    change (laneAlpha m P w (topLayer P w - 1) (s + 1))[_]? = some true at ham
    rw [hA1] at ham
    simpa [word1000, UnitDiagonal.trueIdx] using UnitDiagonal.mem_trueIdx.mpr ham
  have hst : Drift.succ P t = a₀ := by
    have h := (classPhaseAtRank_eq hd hv ha₀m).symm
    rw [ha₀r] at h
    exact h
  exact ⟨t, rfl, hoa₂, hst, hot⟩

private theorem secondInner_W8W9_ports {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (s : Int)
    (hB : laneAlpha m P w (topLayer P w - 2) s = UnitDiagonal.W8 ∨
          laneAlpha m P w (topLayer P w - 2) s = UnitDiagonal.W9) :
    8 ≤ (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 2) s)).length ∧
    UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
      (fun i => decide (inDir w i = .west))) = [4, 5, 7] ∧
    UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
      (fun i => decide (outDir w i = .north))) = [1, 3, 4] ∧
    (UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
        (fun i => decide (outDir w i = .south))) = [0, 2, 5, 6, 7] ∨
      UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
        (fun i => decide (outDir w i = .south))) = [0, 2, 5, 6, 7, 8]) ∧
    (UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
        (fun i => decide (inDir w i = .east))) = [0, 1, 2, 3, 6] ∨
      UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
        (fun i => decide (inDir w i = .east))) = [0, 1, 2, 3, 6, 8]) := by
  have hβB := laneBeta_depth2 h hm hd s
  have hWB : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
      (fun i => decide (inDir w i = .west)) = laneAlpha m P w (topLayer P w - 2) s :=
    lane_incoming_portWord h hm hd 2 s true
  have hEB : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
      (fun i => decide (inDir w i = .east)) = (laneAlpha m P w (topLayer P w - 2) s).map (!·) :=
    lane_incoming_portWord h hm hd 2 s false
  have hNB : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
      (fun i => decide (outDir w i = .north)) = laneBeta m P w (topLayer P w - 2) s :=
    lane_outgoing_portWord h hm hd 2 s true
  have hSB : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 2) s)
      (fun i => decide (outDir w i = .south)) = (laneBeta m P w (topLayer P w - 2) s).map (!·) :=
    lane_outgoing_portWord h hm hd 2 s false
  have hl := classPortWord_length (diagDrift m) P w (laneCell (topLayer P w - 2) s)
    (LangtonsAnt.alpha w)
  change (laneAlpha m P w (topLayer P w - 2) s).length = _ at hl
  rcases hB with h8 | h9
  · refine ⟨?_, ?_, ?_, Or.inl ?_, Or.inl ?_⟩
    · rw [h8] at hl; simp [UnitDiagonal.W8] at hl; omega
    · rw [hWB, h8]; exact UnitDiagonal.W8_trueIdx
    · rw [hNB, hβB, h8]; exact UnitDiagonal.W8_beta_trueIdx
    · rw [hSB, hβB, h8]; exact UnitDiagonal.W8_beta_falseIdx
    · rw [hEB, h8]; exact UnitDiagonal.W8_falseIdx
  · refine ⟨?_, ?_, ?_, Or.inr ?_, Or.inr ?_⟩
    · rw [h9] at hl; simp [UnitDiagonal.W9] at hl; omega
    · rw [hWB, h9]; exact UnitDiagonal.W9_trueIdx
    · rw [hNB, hβB, h9]; exact UnitDiagonal.W9_beta_trueIdx
    · rw [hSB, hβB, h9]; exact UnitDiagonal.W9_beta_falseIdx
    · rw [hEB, h9]; exact UnitDiagonal.W9_falseIdx

private theorem lane_second_to_third_port {m P k rk : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    (hBr : laneAlpha m P w (topLayer P w - 2) r = UnitDiagonal.W8 ∨
           laneAlpha m P w (topLayer P w - 2) r = UnitDiagonal.W9)
    (hrk : rk < (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 2) r)).length)
    (hk : ([0, 2, 5, 6, 7] : List Nat)[k]? = some rk) :
    let b := classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 2) r) rk
    outDir w b = .south ∧
    Drift.succ P b ∈ Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 3) r) ∧
    (UnitDiagonal.trueIdx (laneAlpha m P w (topLayer P w - 3) r))[k]? =
      some (Drift.stableRank P w (Drift.succ P b)) := by
  obtain ⟨_, _, _, hSB, _⟩ := secondInner_W8W9_ports h hm hd r hBr
  have hdep : (UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w
      (laneCell (topLayer P w - 2) r) (fun j => decide (outDir w j = .south))))[k]? = some rk := by
    rcases hSB with h5 | h6
    · rw [h5]; exact hk
    · rw [h6]
      have hlt : k < ([0, 2, 5, 6, 7] : List Nat).length := UnitDiagonal.lt_length_of_getElem? hk
      change ([0, 2, 5, 6, 7] ++ [8])[k]? = some rk
      rw [List.getElem?_append_left hlt]
      exact hk
  have hmBC : Drift.SameClass (diagDrift m)
      (move (laneCell (topLayer P w - 2) r) .south) (laneCell (topLayer P w - 3) r) := by
    rw [move_laneCell_south, show topLayer P w - 2 - 1 = topLayer P w - 3 by omega]
    exact Drift.SameClass.refl _ _
  have hSC : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 3) r)
      (fun j => decide (inDir w j = .south)) = laneAlpha m P w (topLayer P w - 3) r :=
    lane_incoming_portWord h hm hd 3 r true
  have hs := class_succ_of_departure_port h hd (diagDrift_ne_zero hm) hmBC hrk hdep
  rwa [hSC] at hs

private theorem lane_third_to_second_port {m P k rk : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int)
    (hBr1 : laneAlpha m P w (topLayer P w - 2) (r + 1) = UnitDiagonal.W8 ∨
            laneAlpha m P w (topLayer P w - 2) (r + 1) = UnitDiagonal.W9)
    (hrk : rk < (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 2) (r + 1))).length)
    (hk : ([0, 1, 2, 3, 6] : List Nat)[k]? = some rk) :
    let b := classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 2) (r + 1)) rk
    let c := Drift.pred P b
    c ∈ Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 3) r) ∧
    Drift.succ P c = b ∧
    outDir w c = .east ∧
    (UnitDiagonal.trueIdx (laneBeta m P w (topLayer P w - 3) r))[k]? =
      some (Drift.stableRank P w c) := by
  obtain ⟨_, _, _, _, hEB⟩ := secondInner_W8W9_ports h hm hd (r + 1) hBr1
  have harr : (UnitDiagonal.trueIdx (classPortWord (diagDrift m) P w
      (laneCell (topLayer P w - 2) (r + 1)) (fun j => decide (inDir w j = .east))))[k]? = some rk := by
    rcases hEB with h5 | h6
    · rw [h5]; exact hk
    · rw [h6]
      have hlt : k < ([0, 1, 2, 3, 6] : List Nat).length := UnitDiagonal.lt_length_of_getElem? hk
      change ([0, 1, 2, 3, 6] ++ [8])[k]? = some rk
      rw [List.getElem?_append_left hlt]
      exact hk
  have hmCB : Drift.SameClass (diagDrift m)
      (move (laneCell (topLayer P w - 3) r) .east) (laneCell (topLayer P w - 2) (r + 1)) := by
    rw [move_laneCell_east, show topLayer P w - 3 + 1 = topLayer P w - 2 by omega]
    exact Drift.SameClass.refl _ _
  have hEC : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 3) r)
      (fun j => decide (outDir w j = .east)) = laneBeta m P w (topLayer P w - 3) r :=
    lane_outgoing_portWord h hm hd 3 r true
  have hp := class_pred_of_arrival_port h hd (diagDrift_ne_zero hm) hmCB hrk harr
  rwa [hEC] at hp

/-- **Target (2): No three consecutive `1000` lanes on the first inner layer.**
For every `m ≥ 1`, `P > 0`, and `ConsistentWord P w` with full period drift `(m, -m)` — with no
minimality assumption and no global top-layer occupancy assumption — the first-inner-layer
rank-ordered arrival tables `α_r = laneAlpha m P w (topLayer P w - 1) r` cannot satisfy
`α_r = α_{r+1} = α_{r+2} = 1000` for any lane `r`. -/
theorem no_three_consecutive_1000 {m P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m) (r : Int) :
    ¬ (laneAlpha m P w (topLayer P w - 1) r = word1000 ∧
       laneAlpha m P w (topLayer P w - 1) (r + 1) = word1000 ∧
       laneAlpha m P w (topLayer P w - 1) (r + 2) = word1000) := by
  rintro ⟨hA0, hA1, hA2⟩
  have hv := diagDrift_ne_zero hm
  let v := diagDrift m
  have hA2' : laneAlpha m P w (topLayer P w - 1) (r + 1 + 1) = word1000 := by
    rwa [show r + 1 + 1 = r + 2 by omega]
  have hBr := second_inner_W8_or_W9_of_adjacent_1000 h hm hd r hA0 hA1
  have hBr1 := second_inner_W8_or_W9_of_adjacent_1000 h hm hd (r + 1) hA1 hA2'
  obtain ⟨hLA1, hNA1, hWA1⟩ := firstInner_1000_ports h hm hd (r + 1) hA1
  obtain ⟨hLA2, _, hWA2⟩ := firstInner_1000_ports h hm hd (r + 1 + 1) hA2'
  obtain ⟨hLBr, hWBr, _, _, _⟩ := secondInner_W8W9_ports h hm hd r hBr
  obtain ⟨hLBr1, hWBr1, hNBr1, _, _⟩ := secondInner_W8W9_ports h hm hd (r + 1) hBr1
  -- Directed class adjacencies above `C_r`
  have hmB1A1 : Drift.SameClass v (move (laneCell (topLayer P w - 2) (r + 1)) .north) (laneCell (topLayer P w - 1) (r + 1)) := by
    rw [move_laneCell_north, show topLayer P w - 2 + 1 = topLayer P w - 1 by omega]; exact Drift.SameClass.refl _ _
  have hmA1B0 : Drift.SameClass v (move (laneCell (topLayer P w - 1) (r + 1)) .west) (laneCell (topLayer P w - 2) r) := by
    rw [move_laneCell_west, show topLayer P w - 1 - 1 = topLayer P w - 2 by omega, show r + 1 - 1 = r by omega]
    exact Drift.SameClass.refl _ _
  have hmA2B1 : Drift.SameClass v (move (laneCell (topLayer P w - 1) (r + 1 + 1)) .west) (laneCell (topLayer P w - 2) (r + 1)) := by
    rw [move_laneCell_west, show topLayer P w - 1 - 1 = topLayer P w - 2 by omega, show r + 1 + 1 - 1 = r + 1 by omega]
    exact Drift.SameClass.refl _ _
  -- Fixed upper successor edges:
  -- `B_{r+1}[1] --N--> A_{r+1}[1] --W--> B_r[5]`
  -- `B_{r+1}[3] --N--> A_{r+1}[2] --E--> t --S--> A_{r+2}[0] --W--> B_{r+1}[4] --N--> A_{r+1}[3] --W--> B_r[7]`
  obtain ⟨hoB1_1, hsB1_1⟩ := class_succ_phaseAtRank_of_port_match h hd hv hmB1A1
    (r := 1) (s := 1) (k := 0) (by omega) (by omega) (by rw [hNBr1]; rfl) (by rw [hNA1]; rfl)
  obtain ⟨hoA1_1, hsA1_1⟩ := class_succ_phaseAtRank_of_port_match h hd hv hmA1B0
    (r := 1) (s := 5) (k := 1) (by omega) (by omega) (by rw [hWA1]; rfl) (by rw [hWBr]; rfl)
  obtain ⟨hoB1_3, hsB1_3⟩ := class_succ_phaseAtRank_of_port_match h hd hv hmB1A1
    (r := 3) (s := 2) (k := 1) (by omega) (by omega) (by rw [hNBr1]; rfl) (by rw [hNA1]; rfl)
  obtain ⟨t, hsA1_2, hoA1_2, hst, hot⟩ := adjacent_1000_top_bridge h hm hd (r + 1) hA1 hA2'
  obtain ⟨hoA2_0, hsA2_0⟩ := class_succ_phaseAtRank_of_port_match h hd hv hmA2B1
    (r := 0) (s := 4) (k := 0) (by omega) (by omega) (by rw [hWA2]; rfl) (by rw [hWBr1]; rfl)
  obtain ⟨hoB1_4, hsB1_4⟩ := class_succ_phaseAtRank_of_port_match h hd hv hmB1A1
    (r := 4) (s := 3) (k := 2) (by omega) (by omega) (by rw [hNBr1]; rfl) (by rw [hNA1]; rfl)
  obtain ⟨hoA1_3, hsA1_3⟩ := class_succ_phaseAtRank_of_port_match h hd hv hmA1B0
    (r := 3) (s := 7) (k := 2) (by omega) (by omega) (by rw [hWA1]; rfl) (by rw [hWBr]; rfl)
  -- Layer `C_r = laneCell (topLayer P w - 3) r` upper arrival/departure rank lists `p` and `q`
  let αC := laneAlpha m P w (topLayer P w - 3) r
  let βC := laneBeta m P w (topLayer P w - 3) r
  let p := UnitDiagonal.trueIdx αC
  let q := UnitDiagonal.trueIdx βC
  let n := (Drift.classPhases v P w (laneCell (topLayer P w - 3) r)).length
  -- `B_r --S--> C_r` and `C_r --E--> B_{r+1}` matched ports at indices `1, 2, 3, 4`
  obtain ⟨hoB0_2, hsb0_2m, hp1⟩ := lane_second_to_third_port h hm hd r hBr (k := 1) (rk := 2) (by omega) rfl
  obtain ⟨hoB0_5, _, hp2⟩ := lane_second_to_third_port h hm hd r hBr (k := 2) (rk := 5) (by omega) rfl
  obtain ⟨hoB0_7, hsb0_7m, hp4⟩ := lane_second_to_third_port h hm hd r hBr (k := 4) (rk := 7) (by omega) rfl
  obtain ⟨hc1m, hsc1, hoc1, hq1⟩ := lane_third_to_second_port h hm hd r hBr1 (k := 1) (rk := 1) (by omega) rfl
  obtain ⟨hc3m, hsc3, hoc3, hq3⟩ := lane_third_to_second_port h hm hd r hBr1 (k := 3) (rk := 3) (by omega) rfl
  obtain ⟨hc4m, hsc4, hoc4, hq4⟩ := lane_third_to_second_port h hm hd r hBr1 (k := 4) (rk := 6) (by omega) rfl
  have hlp : 5 ≤ p.length := Nat.succ_le_of_lt (UnitDiagonal.lt_length_of_getElem? hp4)
  have hlq : 5 ≤ q.length := Nat.succ_le_of_lt (UnitDiagonal.lt_length_of_getElem? hq4)
  have hp1lt : 1 < p.length := by omega
  have hp2lt : 2 < p.length := by omega
  have hp4lt : 4 < p.length := by omega
  have hq1lt : 1 < q.length := by omega
  have hq3lt : 3 < q.length := by omega
  have hq4lt : 4 < q.length := by omega
  -- Return 1 (`ENWS`): `C_r[q₁] → B_{r+1}[1] → A_{r+1}[1] → B_r[5] → C_r[p₂]` gives `p[2] = q[1] + 1`
  have hret1 := four_step_return_rank hd hv (Drift.mem_classPhases.mp hc1m).1
    hsc1 hsB1_1 hsA1_1 rfl .east .north .west .south hoc1 hoB1_1 hoA1_1 hoB0_5
    UnitDiagonal.firstReturn_ENWS
  have hp2_eq : p[2] = q[1] + 1 := by
    rw [getElem_of_getElem? hp2lt hp2, getElem_of_getElem? hq1lt hq1]
    exact hret1
  -- Return 2 (`ENESWNWS`): `C_r[q₃] → B_{r+1}[3] → A_{r+1}[2] → t → A_{r+2}[0] → B_{r+1}[4] → A_{r+1}[3] → B_r[7] → C_r[p₄]`
  have hret2 := eight_step_return_rank hd hv (Drift.mem_classPhases.mp hc3m).1
    hsc3 hsB1_3 hsA1_2 hst hsA2_0 hsB1_4 hsA1_3 rfl
    .east .north .east .south .west .north .west .south
    hoc3 hoB1_3 hoA1_2 hot hoA2_0 hoB1_4 hoA1_3 hoB0_7
    UnitDiagonal.firstReturn_ENESWNWS
  have hp4_eq : p[4] = q[3] + 1 := by
    rw [getElem_of_getElem? hp4lt hp4, getElem_of_getElem? hq3lt hq3]
    exact hret2
  -- Parity interleaving on odd-depth class `C_r`
  have hβC : βC = UnitDiagonal.beta αC true := laneBeta_depth3 h hm hd r
  have hlenα : αC.length = n := classPortWord_length v P w (laneCell (topLayer P w - 3) r) _
  have hlenβ : βC.length = n := classPortWord_length v P w (laneCell (topLayer P w - 3) r) _
  have hpn : ∀ x ∈ p, x < n := fun x hx => by
    rw [← hlenα]; exact UnitDiagonal.lt_length_of_getElem? (UnitDiagonal.mem_trueIdx.mp hx)
  have hqn : ∀ x ∈ q, x < n := fun x hx => by
    rw [← hlenβ]; exact UnitDiagonal.lt_length_of_getElem? (UnitDiagonal.mem_trueIdx.mp hx)
  have heven : ∀ x, x < n → x % 2 = 0 → (x ∈ p ↔ x ∉ q) := by
    intro x hxn hxe
    have hxα : x < αC.length := by omega
    have hget : αC[x]? = some αC[x] := List.getElem?_eq_getElem hxα
    have hdec : decide (x % 2 = 1) = false := decide_eq_false (by omega)
    have hgetβ : βC[x]? = some (!αC[x]) := by
      rw [hβC, UnitDiagonal.beta_spec, hget, hdec]; cases αC[x] <;> rfl
    simp only [p, q, UnitDiagonal.mem_trueIdx, hget, hgetβ, Option.some.injEq]
    cases αC[x] <;> simp
  have hodd : ∀ x, x < n → x % 2 = 1 → (x ∈ p ↔ x ∈ q) := by
    intro x hxn hxo
    have hxα : x < αC.length := by omega
    have hget : αC[x]? = some αC[x] := List.getElem?_eq_getElem hxα
    have hdec : decide (x % 2 = 1) = true := decide_eq_true hxo
    have hgetβ : βC[x]? = some αC[x] := by
      rw [hβC, UnitDiagonal.beta_spec, hget, hdec]; cases αC[x] <;> rfl
    simp only [p, q, UnitDiagonal.mem_trueIdx, hget, hgetβ]
  -- Apply `UnitDiagonal.interleave_bridge` to force one of the two forbidden bridges
  rcases UnitDiagonal.interleave_bridge p q n
      (UnitDiagonal.pairwise_trueIdx αC) (UnitDiagonal.pairwise_trueIdx βC)
      hpn hqn hlp hlq heven hodd hp2_eq hp4_eq with hbridge1 | hbridge2
  · -- Forbidden bridge 1 (`p[1] = q[1]`): `SENW` returns `B_r[2]` to `B_r[5]`, forcing `5 = 2 + 1`
    have hrank : Drift.stableRank P w (Drift.succ P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) r) 2)) =
        Drift.stableRank P w (Drift.pred P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) (r + 1)) 1)) := by
      rw [← getElem_of_getElem? hp1lt hp1, ← getElem_of_getElem? hq1lt hq1]
      exact hbridge1
    have hbr : Drift.succ P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) r) 2) =
        Drift.pred P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) (r + 1)) 1) :=
      Drift.stableRank_injective_on_class hd hv hsb0_2m hc1m hrank
    have hb2P : classPhaseAtRank v P w (laneCell (topLayer P w - 2) r) 2 < P :=
      (Drift.mem_classPhases.mp (classPhaseAtRank_mem hd hv (by omega))).1
    have hret := four_step_return_rank hd hv hb2P hbr hsc1 hsB1_1 hsA1_1
      .south .east .north .west hoB0_2 hoc1 hoB1_1 hoA1_1 UnitDiagonal.firstReturn_SENW
    rw [classPhaseAtRank_rank hd hv (by omega), classPhaseAtRank_rank hd hv (by omega)] at hret
    omega
  · -- Forbidden bridge 2 (`p[4] = q[4]`): `NWSE` returns `B_{r+1}[4]` to `B_{r+1}[6]`, forcing `6 = 4 + 1`
    have hrank : Drift.stableRank P w (Drift.succ P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) r) 7)) =
        Drift.stableRank P w (Drift.pred P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) (r + 1)) 6)) := by
      rw [← getElem_of_getElem? hp4lt hp4, ← getElem_of_getElem? hq4lt hq4]
      exact hbridge2
    have hbr : Drift.succ P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) r) 7) =
        Drift.pred P (classPhaseAtRank v P w (laneCell (topLayer P w - 2) (r + 1)) 6) :=
      Drift.stableRank_injective_on_class hd hv hsb0_7m hc4m hrank
    have hb4P : classPhaseAtRank v P w (laneCell (topLayer P w - 2) (r + 1)) 4 < P :=
      (Drift.mem_classPhases.mp (classPhaseAtRank_mem hd hv (by omega))).1
    have hret := four_step_return_rank hd hv hb4P hsB1_4 hsA1_3 hbr hsc4
      .north .west .south .east hoB1_4 hoA1_3 hoB0_7 hoc4 UnitDiagonal.firstReturn_NWSE
    rw [classPhaseAtRank_rank hd hv (by omega), classPhaseAtRank_rank hd hv (by omega)] at hret
    omega

/-- Specialization of Target (2) to `m = 2` (drift `(2, -2)`): the two first-inner-layer lanes
cannot both have arrival word `1000`. -/
theorem no_both_lanes_1000_of_m2 {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = diagDrift 2) :
    ¬ (laneAlpha 2 P w (topLayer P w - 1) 0 = word1000 ∧
       laneAlpha 2 P w (topLayer P w - 1) 1 = word1000) := by
  rintro ⟨h0, h1⟩
  have h2 : laneAlpha 2 P w (topLayer P w - 1) (0 + 2) = word1000 := by
    simpa using (laneAlpha_periodic 2 P w (topLayer P w - 1) 0).trans h0
  exact no_three_consecutive_1000 h (by decide) hd 0 ⟨h0, h1, h2⟩

/-- Specialization of Target (2) to `m = 1` (unit diagonal drift `(1, -1)`): the unique
first-inner-layer lane cannot have arrival word `1000`. -/
theorem no_lane_1000_of_m1 {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = diagDrift 1) :
    laneAlpha 1 P w (topLayer P w - 1) 0 ≠ word1000 := by
  intro h0
  have h1 : laneAlpha 1 P w (topLayer P w - 1) (0 + 1) = word1000 :=
    (laneAlpha_periodic 1 P w (topLayer P w - 1) 0).trans h0
  have h2 : laneAlpha 1 P w (topLayer P w - 1) (0 + 2) = word1000 := by
    have hp := laneAlpha_periodic 1 P w (topLayer P w - 1) 1
    simpa only [show (1 : Int) + (1 : Nat) = 0 + 2 by omega] using hp.trans h1
  exact no_three_consecutive_1000 h (by decide) hd 0 ⟨h0, h1, h2⟩


end DiagonalMultipleLanes
end LangtonsAnt
