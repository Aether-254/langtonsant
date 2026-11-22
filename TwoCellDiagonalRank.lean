import TwoCellDiagonalExtremal
import TwoCellDiagonalGadget

/-!
# Instantiation of `PortInversion` L14/L16 on `(2, -2)` quotient classes (L23)

This module instantiates `PortInversion` items L14 (`portWord_parity`) and L16 (block-permutation
inversion parity via `TwoCellDiagonalParity` and `TwoCellDiagonalGadget`) on the rank-sorted
`(2, -2)` translation classes `(t, r)` ordered lexicographically by `(t, r, port)` (zero `sorry`,
zero `axiom`, zero `native_decide`):

- `depBlock_map_succ_eq_arrBlock`: cyclic successor maps rank-sorted departures onto rank-sorted
  arrivals identically on every quotient edge.
- `portWord_inversions_parity`: `1 + ∑_v (wordInv α_v + wordInv β_v) + E ≡ 0 (mod 2)`.
- `leftRankSum_parity_general`: `leftRankSum P w + 1 + E + totalLocalCorr ≡ 0 (mod 2)` for every
  `(2, -2)` consistent word (of arbitrary growth `g`).
- `pureOdd_leftRankSum_parity` & `pureOdd_edgeCross_eq_chain` (**L23**): under `PureOddWake`,
  `leftRankSum P w % 2 = (1 + E) % 2` and `E % 2 = ∑_{j, r} (n_{j,r} + n_{j,r} · n_{j+2,r}) % 2`.
-/

namespace LangtonsAnt
namespace TwoCellDiagonal

/-- Phase in class `(t, r)` at `stableRank = k` (default `0` out of range). -/
def phaseOfRank (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) (k : Nat) : Nat :=
  ((classPhases2 P w t r).filter (fun i => decide (Drift.stableRank P w i = k))).headD 0

/-- Phases in `(2, -2)` class `(t, r)` listed in strictly increasing `stableRank` order. -/
def rankedClassPhases (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : List Nat :=
  (List.range (classMult P w t r)).map (phaseOfRank P w t r)

/-- Uniform incoming port bit (`true` for `.north` at even layers, `.east` at odd layers). -/
def inPortBit (w : Nat → Bool) (i : Nat) : Bool :=
  if layer (wordPos w i) % 2 = 0 then decide (inDir w i = .north) else decide (inDir w i = .east)

/-- Uniform outgoing port bit (`true` for `.east` at even layers, `.north` at odd layers). -/
def outPortBit (w : Nat → Bool) (i : Nat) : Bool :=
  if layer (wordPos w i) % 2 = 0 then decide (outDir w i = .east) else decide (outDir w i = .north)

/-- Rank-sorted departures along quotient edge `e`. -/
def depBlock (P : Nat) (w : Nat → Bool) (e : GEdge) : List Nat :=
  (rankedClassPhases P w e.srcLayer e.srcLane).filter (fun i => decide (outDir w i = e.dir))

/-- Rank-sorted arrivals along quotient edge `e`. -/
def arrBlock (P : Nat) (w : Nat → Bool) (e : GEdge) : List Nat :=
  (rankedClassPhases P w e.dstLayer e.dstLane).filter (fun i => decide (inDir w i = e.dir))

/-- Edge multiplicity `depCount` on quotient edge `e`. -/
def edgeMult (P : Nat) (w : Nat → Bool) (e : GEdge) : Nat :=
  depCount P w e.srcLayer e.srcLane e.dir

private theorem list_eq_singleton_of_nodup_mem {α : Type} {l : List α} {a : α}
    (hnd : l.Nodup) (ha : a ∈ l) (huniq : ∀ b ∈ l, b = a) : l = [a] := by
  cases l with
  | nil => simp at ha
  | cons x xs =>
    have hx : x = a := huniq x (by simp)
    subst hx
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hy : y = x := huniq y (by simp)
      subst hy
      exact False.elim ((List.nodup_cons.mp hnd).1 (by simp))

private theorem phaseOfRank_spec {P k : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (hd : wordDrift P w = (2, -2)) (hk : k < classMult P w t r) :
    phaseOfRank P w t r k ∈ classPhases2 P w t r ∧
    Drift.stableRank P w (phaseOfRank P w t r k) = k := by
  obtain ⟨i, hiC, hir⟩ :=
    Drift.stableRank_surjective_on_class (v := (2, -2)) (c := classRep t r) hd
      drift_two_negTwo_ne_zero hk
  have hfilt :
      (classPhases2 P w t r).filter (fun j => decide (Drift.stableRank P w j = k)) = [i] := by
    apply list_eq_singleton_of_nodup_mem ((classPhases2_nodup P w t r).filter _)
    · exact List.mem_filter.mpr ⟨hiC, decide_eq_true hir⟩
    · intro j hj
      obtain ⟨hjC, hjr⟩ := List.mem_filter.mp hj
      exact Drift.stableRank_injective_on_class hd drift_two_negTwo_ne_zero hjC hiC
        ((of_decide_eq_true hjr).trans hir.symm)
  unfold phaseOfRank
  rw [hfilt]
  exact ⟨hiC, hir⟩

private theorem rankedClassPhases_pairwise_lt {P : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (hd : wordDrift P w = (2, -2)) :
    (rankedClassPhases P w t r).Pairwise (fun a b => Drift.stableRank P w a < Drift.stableRank P w b) := by
  unfold rankedClassPhases
  rw [List.pairwise_map]
  have hlt : ∀ m : Nat, m ≤ classMult P w t r →
      (List.range m).Pairwise (fun a b =>
        Drift.stableRank P w (phaseOfRank P w t r a) <
          Drift.stableRank P w (phaseOfRank P w t r b)) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.pairwise_append]
      refine ⟨ih (by omega), List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      have ha' : a < m := List.mem_range.mp ha
      simp only [List.mem_singleton] at hb; subst hb
      rw [(phaseOfRank_spec hd (by omega)).2, (phaseOfRank_spec hd (by omega)).2]
      exact ha'
  exact hlt (classMult P w t r) (Nat.le_refl _)

private theorem rankedClassPhases_nodup {P : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (hd : wordDrift P w = (2, -2)) :
    (rankedClassPhases P w t r).Nodup :=
  (rankedClassPhases_pairwise_lt hd).imp (fun {a b} h heq => by rw [heq] at h; exact Nat.lt_irrefl _ h)

private theorem rankedClassPhases_perm {P : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (hd : wordDrift P w = (2, -2)) :
    (rankedClassPhases P w t r).Perm (classPhases2 P w t r) := by
  apply (List.perm_ext_iff_of_nodup (rankedClassPhases_nodup hd) (classPhases2_nodup P w t r)).mpr
  intro i
  unfold rankedClassPhases
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (phaseOfRank_spec hd (List.mem_range.mp hk)).1
  · intro hiC
    have hlt : Drift.stableRank P w i < classMult P w t r :=
      Drift.stableRank_lt_class_length hd drift_two_negTwo_ne_zero hiC
    refine ⟨Drift.stableRank P w i, List.mem_range.mpr hlt, ?_⟩
    have hs := phaseOfRank_spec hd hlt
    exact Drift.stableRank_injective_on_class hd drift_two_negTwo_ne_zero hs.1 hiC hs.2

private theorem rankSum_rankedClassPhases {P : Nat} {w : Nat → Bool} {t : Int} {r : Bool}
    (hd : wordDrift P w = (2, -2)) (p : Nat → Bool) :
    PortInversion.rankSum ((rankedClassPhases P w t r).map p) =
      (((classPhases2 P w t r).filter p).map (Drift.stableRank P w)).sum := by
  unfold rankedClassPhases
  rw [rankSum_map_range]
  have heq :
      (List.range (classMult P w t r)).filter (fun k => p (phaseOfRank P w t r k)) =
      (((List.range (classMult P w t r)).map (phaseOfRank P w t r)).filter p).map
        (Drift.stableRank P w) := by
    rw [List.filter_map, List.map_map]
    symm
    have hm :
        ((List.range (classMult P w t r)).filter (p ∘ phaseOfRank P w t r)).map
          (Drift.stableRank P w ∘ phaseOfRank P w t r) =
        ((List.range (classMult P w t r)).filter (p ∘ phaseOfRank P w t r)).map id := by
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.mp (List.mem_filter.mp hk).1
      exact (phaseOfRank_spec hd hk').2
    rw [hm, List.map_id]
    rfl
  rw [heq]
  exact PortInversion.perm_sum (((rankedClassPhases_perm hd).filter p).map (Drift.stableRank P w))

private theorem edge_sameClass_move (e : GEdge) :
    Drift.SameClass (2, -2) (move (classRep e.srcLayer e.srcLane) e.dir)
      (classRep e.dstLayer e.dstLane) := by
  rcases e with ⟨j, r, k⟩
  cases k
  · exact sameClass_move_classRep_north j r
  · simpa [GEdge.srcLayer, GEdge.srcLane, GEdge.dstLayer, GEdge.dstLane, GEdge.dir] using
      sameClass_move_classRep_west (j + 1) (!r)
  · simpa [GEdge.srcLayer, GEdge.srcLane, GEdge.dstLayer, GEdge.dstLane, GEdge.dir,
      show j + 1 + 1 = j + 2 by omega] using
      sameClass_move_classRep_east (j + 1) (!r)
  · simpa [GEdge.srcLayer, GEdge.srcLane, GEdge.dstLayer, GEdge.dstLane, GEdge.dir,
      show j + 2 - 1 = j + 1 by omega] using
      sameClass_move_classRep_south (j + 2) r

private theorem depBlock_perm_departures {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (e : GEdge) :
    (depBlock P w e).Perm (Drift.departures (2, -2) P w (classRep e.srcLayer e.srcLane) e.dir) :=
  (rankedClassPhases_perm hd).filter _

private theorem arrBlock_perm_arrivals {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (e : GEdge) :
    (arrBlock P w e).Perm (Drift.arrivals (2, -2) P w (classRep e.dstLayer e.dstLane) e.dir) :=
  (rankedClassPhases_perm hd).filter _

private theorem arrBlock_length {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2)) (e : GEdge) :
    (arrBlock P w e).length = edgeMult P w e := by
  rw [(arrBlock_perm_arrivals hd e).length_eq]
  rw [← Drift.arrivals_congr P w e.dir (edge_sameClass_move e)]
  exact (Drift.departures_length_eq_arrivals_length hh hd).symm

private theorem nodup_map_on_dep {α β : Type} {xs : List α} {f : α → β}
    (hn : xs.Nodup) (hf : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hn (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy]))⟩
    intro h
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    have := hf b (by simp [hb]) a (by simp) he
    subst b; exact ha hb

/-- On every quotient edge `e`, mapping `Drift.succ P` over the rank-sorted departures `depBlock`
equals the rank-sorted arrivals `arrBlock` identically. -/
theorem depBlock_map_succ_eq_arrBlock {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2)) (e : GEdge) :
    (depBlock P w e).map (Drift.succ P) = arrBlock P w e := by
  apply eq_of_perm_of_pairwise_lt (Drift.stableRank P w)
  · have hnd1 : ((depBlock P w e).map (Drift.succ P)).Nodup := by
      apply nodup_map_on_dep ((rankedClassPhases_nodup hd).filter _)
      intro x hx y hy hxy
      have hx' := (depBlock_perm_departures hd e).mem_iff.mp hx
      have hy' := (depBlock_perm_departures hd e).mem_iff.mp hy
      exact UnitDiagonalMatching.succ_injective (Drift.mem_departures.mp hx').1
        (Drift.mem_departures.mp hy').1 hxy
    have hnd2 : (arrBlock P w e).Nodup := (rankedClassPhases_nodup hd).filter _
    apply (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr
    intro j
    rw [List.mem_map, (arrBlock_perm_arrivals hd e).mem_iff,
      ← Drift.arrivals_congr P w e.dir (edge_sameClass_move e), Drift.successor_onto hh hd]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (depBlock_perm_departures hd e).mem_iff.mp hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (depBlock_perm_departures hd e).mem_iff.mpr hi, rfl⟩
  · rw [List.pairwise_map]
    have hpw : (depBlock P w e).Pairwise (fun a b => Drift.stableRank P w a < Drift.stableRank P w b) :=
      (rankedClassPhases_pairwise_lt hd).filter _
    exact hpw.imp_of_mem (fun {a b} ha hb hlt =>
      (Drift.successor_rank_order hd drift_two_negTwo_ne_zero
        ((depBlock_perm_departures hd e).mem_iff.mp ha)
        ((depBlock_perm_departures hd e).mem_iff.mp hb)).mp hlt)
  · exact (rankedClassPhases_pairwise_lt hd).filter _

private theorem stablePart_out_eq_windowOutEdges {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {v : Int × Bool} (hv : v ∈ windowVertices (botLayer P w) (layerWidth P w / 2).toNat) :
    ((windowOutEdges (botLayer P w) (layerWidth P w / 2).toNat v).map (depBlock P w)).flatten =
      PortInversion.stablePart (outPortBit w) (rankedClassPhases P w v.1 v.2) := by
  rcases v with ⟨t, r⟩
  have htop_eq : botLayer P w + 2 * (((layerWidth P w / 2).toNat : Nat) : Int) = topLayer P w := by
    have ht := topLayer_odd h hd
    have hb := botLayer_odd h hd
    have hw := layerWidth_ge_two h hd
    unfold layerWidth at hw ⊢; omega
  obtain ⟨hlo, hhi⟩ := mem_windowVertices.mp hv
  rw [htop_eq] at hhi
  have hmem_src : ∀ i ∈ rankedClassPhases P w t r, layer (wordPos w i) = t := fun i hi =>
    (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hi)).2.1
  unfold windowOutEdges PortInversion.stablePart
  by_cases ht : t % 2 = 0
  · simp only [ht, ite_true, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, depBlock, GEdge.srcLayer, GEdge.srcLane, GEdge.dir, Bool.not_not,
      show t - 1 + 1 = t by omega]
    congr 1
    · apply List.filter_congr
      intro i hi
      have hli := hmem_src i hi
      have hdir := (even_layer_dirs ht ((rankedClassPhases_perm hd).mem_iff.mp hi)).2
      unfold outPortBit
      rw [hli, ite_eq_left ht]
      rcases hdir with ho | ho <;> simp [ho]
    · apply List.filter_congr
      intro i hi
      have hli := hmem_src i hi
      unfold outPortBit
      rw [hli, ite_eq_left ht]
      rfl
  · have hodd : t % 2 = 1 := by omega
    simp only [ht, ite_false, htop_eq, List.map_append, List.flatten_append]
    congr 1
    · by_cases hgt : botLayer P w < t
      · simp only [hgt, ite_true, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, depBlock, GEdge.srcLayer, GEdge.srcLane, GEdge.dir,
          show t - 2 + 2 = t by omega]
        apply List.filter_congr
        intro i hi
        have hli := hmem_src i hi
        have hdir := (odd_layer_dirs hodd ((rankedClassPhases_perm hd).mem_iff.mp hi)).2
        unfold outPortBit
        rw [hli, ite_eq_right ht]
        rcases hdir with ho | ho <;> simp [ho]
      · have hbot : t = botLayer P w := by omega
        subst hbot
        simp only [hgt, ite_false, List.map_nil, List.flatten_nil]
        symm
        rw [List.filter_eq_nil_iff]
        intro i hi
        have hli := hmem_src i hi
        have hiP := (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hi)).1
        have hout := (botLayer_phase_rigid h hd hiP hli).2.2.2.1
        unfold outPortBit
        rw [hli, ite_eq_right ht, hout]
        decide
    · by_cases hlt : t < topLayer P w
      · simp only [hlt, ite_true, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, depBlock, GEdge.srcLayer, GEdge.srcLane, GEdge.dir]
        apply List.filter_congr
        intro i hi
        have hli := hmem_src i hi
        unfold outPortBit
        rw [hli, ite_eq_right ht]
        rfl
      · have htop : t = topLayer P w := by omega
        subst htop
        simp only [hlt, ite_false, List.map_nil, List.flatten_nil]
        symm
        rw [List.filter_eq_nil_iff]
        intro i hi
        have hli := hmem_src i hi
        have hiP := (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hi)).1
        have hout := (topLayer_phase_rigid h hd hiP hli).2.2.2.1
        unfold outPortBit
        rw [hli, ite_eq_right ht, hout]
        decide

private theorem stablePart_in_eq_windowInEdges {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2))
    {v : Int × Bool} (hv : v ∈ windowVertices (botLayer P w) (layerWidth P w / 2).toNat) :
    ((windowInEdges (botLayer P w) (layerWidth P w / 2).toNat v).map (arrBlock P w)).flatten =
      PortInversion.stablePart (inPortBit w) (rankedClassPhases P w v.1 v.2) := by
  rcases v with ⟨t, r⟩
  have htop_eq : botLayer P w + 2 * (((layerWidth P w / 2).toNat : Nat) : Int) = topLayer P w := by
    have ht := topLayer_odd h hd
    have hb := botLayer_odd h hd
    have hw := layerWidth_ge_two h hd
    unfold layerWidth at hw ⊢; omega
  obtain ⟨hlo, hhi⟩ := mem_windowVertices.mp hv
  rw [htop_eq] at hhi
  have hmem_dst : ∀ i ∈ rankedClassPhases P w t r, layer (wordPos w i) = t := fun i hi =>
    (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hi)).2.1
  unfold windowInEdges PortInversion.stablePart
  by_cases ht : t % 2 = 0
  · simp only [ht, ite_true, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, arrBlock, GEdge.dstLayer, GEdge.dstLane, GEdge.dir,
      show t - 1 + 1 = t by omega]
    congr 1
    · apply List.filter_congr
      intro i hi
      have hli := hmem_dst i hi
      have hdir := (even_layer_dirs ht ((rankedClassPhases_perm hd).mem_iff.mp hi)).1
      unfold inPortBit
      rw [hli, ite_eq_left ht]
      rcases hdir with hi' | hi' <;> simp [hi']
    · apply List.filter_congr
      intro i hi
      have hli := hmem_dst i hi
      unfold inPortBit
      rw [hli, ite_eq_left ht]
      rfl
  · have hodd : t % 2 = 1 := by omega
    simp only [ht, ite_false, htop_eq, List.map_append, List.flatten_append]
    congr 1
    · by_cases hlt : t < topLayer P w
      · simp only [hlt, ite_true, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, arrBlock, GEdge.dstLayer, GEdge.dstLane, GEdge.dir]
        apply List.filter_congr
        intro i hi
        have hli := hmem_dst i hi
        have hdir := (odd_layer_dirs hodd ((rankedClassPhases_perm hd).mem_iff.mp hi)).1
        unfold inPortBit
        rw [hli, ite_eq_right ht]
        rcases hdir with hi' | hi' <;> simp [hi']
      · have htop : t = topLayer P w := by omega
        subst htop
        simp only [hlt, ite_false, List.map_nil, List.flatten_nil]
        symm
        rw [List.filter_eq_nil_iff]
        intro i hi
        have hli := hmem_dst i hi
        have hiP := (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hi)).1
        have hin := (topLayer_phase_rigid h hd hiP hli).2.2.1
        unfold inPortBit
        rw [hli, ite_eq_right ht, hin]
        decide
    · by_cases hgt : botLayer P w < t
      · simp only [hgt, ite_true, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, arrBlock, GEdge.dstLayer, GEdge.dstLane, GEdge.dir,
          show t - 2 + 2 = t by omega]
        apply List.filter_congr
        intro i hi
        have hli := hmem_dst i hi
        unfold inPortBit
        rw [hli, ite_eq_right ht]
        rfl
      · have hbot : t = botLayer P w := by omega
        subst hbot
        simp only [hgt, ite_false, List.map_nil, List.flatten_nil]
        symm
        rw [List.filter_eq_nil_iff]
        intro i hi
        have hli := hmem_dst i hi
        have hiP := (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hi)).1
        have hin := (botLayer_phase_rigid h hd hiP hli).2.2.1
        unfold inPortBit
        rw [hli, ite_eq_right ht, hin]
        decide

private theorem flatten_map_flatMap {α β γ : Type} (xs : List α) (f : α → List β) (g : β → List γ) :
    ((xs.flatMap f).map g).flatten = (xs.map (fun a => ((f a).map g).flatten)).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.flatten_append, List.map_cons,
      List.flatten_cons, ih]

private theorem nodup_flatten_of_disjoint' {α : Type} (L : List (List α))
    (hnd : ∀ xs ∈ L, xs.Nodup)
    (hdisj : L.Pairwise (fun xs ys => ∀ a ∈ xs, a ∉ ys)) :
    L.flatten.Nodup := by
  induction L with
  | nil => simp
  | cons xs L ih =>
    rw [List.flatten_cons, List.nodup_append]
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisj
    refine ⟨hnd xs (by simp), ih (fun ys hys => hnd ys (by simp [hys])) htail, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨ys, hys, hay⟩ := List.mem_flatten.mp hb
    exact hhead ys hys a ha hay

private theorem vblocks_flatten_perm_range {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    (((windowVertices (botLayer P w) (layerWidth P w / 2).toNat).map
      (fun v => rankedClassPhases P w v.1 v.2)).flatten).Perm (List.range P) := by
  let j0 := botLayer P w
  let m := (layerWidth P w / 2).toNat
  have htop_eq : j0 + 2 * (m : Int) = topLayer P w := by
    have ht := topLayer_odd h hd
    have hb := botLayer_odd h hd
    have hw := layerWidth_ge_two h hd
    dsimp [j0, m]; unfold layerWidth at hw ⊢; omega
  have hnd : (((windowVertices j0 m).map (fun v => rankedClassPhases P w v.1 v.2)).flatten).Nodup := by
    apply nodup_flatten_of_disjoint'
    · intro xs hxs
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hxs
      exact rankedClassPhases_nodup hd
    · rw [List.pairwise_map]
      exact (windowVertices_nodup j0 m).imp (fun {v1 v2} hne a ha1 ha2 => by
        obtain ⟨_, hl1, hr1⟩ := mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp ha1)
        obtain ⟨_, hl2, hr2⟩ := mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp ha2)
        exact hne (Prod.ext (hl1.symm.trans hl2) (hr1.symm.trans hr2)))
  apply (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr
  intro i
  rw [List.mem_flatten, List.mem_range]
  constructor
  · rintro ⟨xs, hxs, hix⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hxs
    exact (mem_classPhases2.mp ((rankedClassPhases_perm hd).mem_iff.mp hix)).1
  · intro hiP
    refine ⟨rankedClassPhases P w (layer (wordPos w i)) (lane (wordPos w i)), ?_, ?_⟩
    · refine List.mem_map.mpr ⟨(layer (wordPos w i), lane (wordPos w i)), ?_, rfl⟩
      exact mem_windowVertices.mpr ⟨botLayer_le_layer hiP, by rw [htop_eq]; exact layer_le_topLayer hiP⟩
    · exact (rankedClassPhases_perm hd).mem_iff.mpr (mem_classPhases2.mpr ⟨hiP, rfl, rfl⟩)

/-- **L16 instantiated on `(2, -2)` quotient classes:** The sum of incoming and outgoing port-word
inversion counts over all vertices in `[botLayer, topLayer]` plus `1 + E` is even, where `E` is
`pairInvSum edgeSrcLt edgeDstLt (edgeMult P w)` over `gadgetStack`. -/
theorem portWord_inversions_parity {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    let j0 := botLayer P w
    let m := (layerWidth P w / 2).toNat
    (1 +
      ((windowVertices j0 m).map (fun v =>
        PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (inPortBit w)) +
        PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (outPortBit w)))).sum +
      pairInvSum edgeSrcLt edgeDstLt (edgeMult P w) (gadgetStack j0 m)) % 2 = 0 := by
  intro j0 m
  let Vblocks := (windowVertices j0 m).map (fun v => rankedClassPhases P w v.1 v.2)
  let srcBlks := (windowSrcOrder j0 m).map (depBlock P w)
  let dstBlks := (windowDstOrder j0 m).map (arrBlock P w)
  let srcMapped := (windowSrcOrder j0 m).map (arrBlock P w)
  have hj0_odd : j0 % 2 = 1 := botLayer_odd h hd
  have hsrc_flat :
      srcBlks.flatten = (Vblocks.map (PortInversion.stablePart (outPortBit w))).flatten := by
    dsimp [srcBlks, Vblocks, windowSrcOrder]
    rw [flatten_map_flatMap, List.map_map]
    congr 1; apply List.map_congr_left
    intro v hv; exact stablePart_out_eq_windowOutEdges h hd hv
  have hdst_flat :
      dstBlks.flatten = (Vblocks.map (PortInversion.stablePart (inPortBit w))).flatten := by
    dsimp [dstBlks, Vblocks, windowDstOrder]
    rw [flatten_map_flatMap, List.map_map]
    congr 1; apply List.map_congr_left
    intro v hv; exact stablePart_in_eq_windowInEdges h hd hv
  have hperm_sp : ∀ (k : Nat → Bool) (bs : List (List Nat)),
      (bs.map (PortInversion.stablePart k)).flatten.Perm bs.flatten := by
    intro k bs
    induction bs with
    | nil => exact List.Perm.nil
    | cons b bs ibs =>
      simp only [List.map_cons, List.flatten_cons]
      exact (PortInversion.stablePart_perm k b).append ibs
  have hV_perm_range : Vblocks.flatten.Perm (List.range P) := vblocks_flatten_perm_range h hd
  have hsrc_perm_range : srcBlks.flatten.Perm (List.range P) :=
    (hsrc_flat ▸ hperm_sp (outPortBit w) Vblocks).trans hV_perm_range
  have hdst_nd : dstBlks.flatten.Nodup :=
    ((hdst_flat ▸ hperm_sp (inPortBit w) Vblocks).trans hV_perm_range).symm.nodup List.nodup_range
  have hV_nd : ∀ b ∈ Vblocks, b.Nodup := by
    intro b hb; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb; exact rankedClassPhases_nodup hd
  have hsrc_inv :
      (PortInversion.listInv srcBlks.flatten +
        (Vblocks.map (fun b => PortInversion.wordInv (b.map (outPortBit w)))).sum) % 2 =
      PortInversion.listInv Vblocks.flatten % 2 := by
    rw [hsrc_flat, PortInversion.listInv_flatten, PortInversion.pairCross_map_stablePart,
      PortInversion.listInv_flatten, List.map_map]
    have hsum := PortInversion.sum_mod_two_congr
      (fun b => PortInversion.listInv (PortInversion.stablePart (outPortBit w) b))
      (fun b => PortInversion.wordInv (b.map (outPortBit w)))
      PortInversion.listInv Vblocks
      (fun b hb => PortInversion.stablePart_parity (outPortBit w) b (hV_nd b hb))
    change ((Vblocks.map (fun b => PortInversion.listInv (PortInversion.stablePart (outPortBit w) b))).sum +
      PortInversion.pairCross Vblocks +
      (Vblocks.map (fun b => PortInversion.wordInv (b.map (outPortBit w)))).sum) % 2 = _
    omega
  have hdst_inv :
      (PortInversion.listInv dstBlks.flatten +
        (Vblocks.map (fun b => PortInversion.wordInv (b.map (inPortBit w)))).sum) % 2 =
      PortInversion.listInv Vblocks.flatten % 2 := by
    rw [hdst_flat, PortInversion.listInv_flatten, PortInversion.pairCross_map_stablePart,
      PortInversion.listInv_flatten, List.map_map]
    have hsum := PortInversion.sum_mod_two_congr
      (fun b => PortInversion.listInv (PortInversion.stablePart (inPortBit w) b))
      (fun b => PortInversion.wordInv (b.map (inPortBit w)))
      PortInversion.listInv Vblocks
      (fun b hb => PortInversion.stablePart_parity (inPortBit w) b (hV_nd b hb))
    change ((Vblocks.map (fun b => PortInversion.listInv (PortInversion.stablePart (inPortBit w) b))).sum +
      PortInversion.pairCross Vblocks +
      (Vblocks.map (fun b => PortInversion.wordInv (b.map (inPortBit w)))).sum) % 2 = _
    omega
  have hmap_flat : srcMapped.flatten = srcBlks.flatten.map (Drift.succ P) := by
    dsimp [srcMapped, srcBlks]
    rw [List.map_flatten, List.map_map]
    congr 1; apply List.map_congr_left
    intro e _; exact (depBlock_map_succ_eq_arrBlock h.1 hd e).symm
  have hcycle :
      (PortInversion.listInv srcMapped.flatten + PortInversion.listInv srcBlks.flatten) % 2 = 1 := by
    rw [hmap_flat, listInv_map_succ_parity h.pos_period hsrc_perm_range]
    have hev := h.even; have hpos := h.pos_period; omega
  have hperm_edges := windowSrcOrder_perm_windowDstOrder hj0_odd m
  have hmap_dst_inv :
      (PortInversion.listInv srcMapped.flatten + PortInversion.listInv dstBlks.flatten) % 2 =
      (PortInversion.pairCross srcMapped + PortInversion.pairCross dstBlks) % 2 := by
    rw [PortInversion.listInv_flatten, PortInversion.listInv_flatten]
    have hps : (srcMapped.map PortInversion.listInv).sum = (dstBlks.map PortInversion.listInv).sum :=
      PortInversion.perm_sum ((hperm_edges.map (arrBlock P w)).map PortInversion.listInv)
    omega
  have hpc_eq :
      (PortInversion.pairCross srcMapped + PortInversion.pairCross dstBlks) % 2 =
      pairInvSum edgeSrcLt edgeDstLt (edgeMult P w) (gadgetStack j0 m) % 2 := by
    have hodd_dst : ∀ e ∈ windowDstOrder j0 m, e.j % 2 = 1 := fun e he =>
      ((mem_gadgetStack_iff hj0_odd).mp ((mem_windowDstOrder_iff hj0_odd).mp he)).1
    have hodd_src : ∀ e ∈ windowSrcOrder j0 m, e.j % 2 = 1 := fun e he =>
      ((mem_gadgetStack_iff hj0_odd).mp ((mem_windowSrcOrder_iff hj0_odd).mp he)).1
    have hpc := pairCross_perm_parity edgeDstLt (arrBlock P w)
      (windowDstOrder j0 m) (windowSrcOrder j0 m)
      hperm_edges (windowDstOrder_nodup j0 m) (windowDstOrder_pairwise j0 m)
      (fun a ha b hb => edgeDstLt_asym_of_odd (hodd_dst a ha) (hodd_dst b hb))
      hdst_nd
    rw [hpc, edgePairInv_eq_pairInvSum edgeSrcLt edgeDstLt _ (windowSrcOrder j0 m)
      (windowSrcOrder_nodup j0 m) (windowSrcOrder_pairwise j0 m)
      (fun a ha b hb => edgeDstLt_total_of_odd (hodd_src a ha) (hodd_src b hb))]
    have hwt_eq : (fun e => (arrBlock P w e).length) = edgeMult P w :=
      funext (arrBlock_length h.1 hd)
    rw [hwt_eq, pairInvSum_perm_on edgeSrcLt edgeDstLt (edgeMult P w) (P := fun e => e.j % 2 = 1)
      (fun a b ha hb => edgeInvBit_symm_of_odd ha hb)
      (windowSrcOrder_perm_gadgetStack hj0_odd m) hodd_src]
  have hsum_combine :
      (Vblocks.map (fun b => PortInversion.wordInv (b.map (inPortBit w)))).sum +
      (Vblocks.map (fun b => PortInversion.wordInv (b.map (outPortBit w)))).sum =
      ((windowVertices j0 m).map (fun v =>
        PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (inPortBit w)) +
        PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (outPortBit w)))).sum := by
    dsimp [Vblocks]
    rw [List.map_map, List.map_map]
    have hadd : ∀ (xs : List (Int × Bool)) (f g : Int × Bool → Nat),
        (xs.map f).sum + (xs.map g).sum = (xs.map (fun v => f v + g v)).sum := by
      intro xs f g
      induction xs with
      | nil => rfl
      | cons x xs ixs => simp only [List.map_cons, List.sum_cons]; omega
    exact hadd (windowVertices j0 m) _ _
  omega

/-! ### Applying L14 (`portWord_parity`) vertex-by-vertex and cancelling `pairCount` terms -/

/-- Sum of `stableRank` over black-read (left-turn) phases in class `(t, r)`. -/
def localLeftRankSum (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat :=
  (((classPhases2 P w t r).filter (fun i => w i)).map (Drift.stableRank P w)).sum

/-- Incoming positive-port binomial term `pairCount A_v` at `(t, r)`. -/
def inPairCount (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat :=
  if t % 2 = 0 then
    PortInversion.pairCount (nCnt P w (t - 1) r)
  else
    PortInversion.pairCount (eCnt P w (t - 1) (!r))

/-- Outgoing positive-port binomial term `pairCount B_v` at `(t, r)`. -/
def outPairCount (P : Nat) (w : Nat → Bool) (t : Int) (r : Bool) : Nat :=
  if t % 2 = 0 then
    PortInversion.pairCount (eCnt P w t r)
  else
    PortInversion.pairCount (nCnt P w t r)

private theorem sum_filter_xor_mod_two {α : Type} (p q : α → Bool) (f : α → Nat) (xs : List α) :
    (((xs.filter (fun x => xor (p x) (q x))).map f).sum) % 2 =
      (((xs.filter p).map f).sum + ((xs.filter q).map f).sum) % 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

private theorem sum_filter_add_not {α : Type} (p : α → Bool) (f : α → Nat) (xs : List α) :
    ((xs.filter p).map f).sum + ((xs.filter (fun x => !p x)).map f).sum = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp] <;> omega

private theorem sum_range_eq_pairCount (n : Nat) :
    (List.range n).sum = PortInversion.pairCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.sum_append, List.sum_singleton, ih, PortInversion.pairCount_succ]

private theorem vertex_portWord_parity {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (t : Int) (r : Bool) :
    (PortInversion.wordInv ((rankedClassPhases P w t r).map (inPortBit w)) +
      PortInversion.wordInv ((rankedClassPhases P w t r).map (outPortBit w)) +
      localLeftRankSum P w t r + localCorr P w t r +
      inPairCount P w t r + outPairCount P w t r) % 2 = 0 := by
  let V := rankedClassPhases P w t r
  have hL14_in := PortInversion.portWord_parity (V.map (inPortBit w))
  have hL14_out := PortInversion.portWord_parity (V.map (outPortBit w))
  have hlen : V.length = classMult P w t r := (rankedClassPhases_perm hd).length_eq
  rw [List.length_map, hlen] at hL14_in hL14_out
  rw [PortInversion.countTrue_map] at hL14_in hL14_out
  have hA_perm : (V.filter (inPortBit w)).length = ((classPhases2 P w t r).filter (inPortBit w)).length :=
    ((rankedClassPhases_perm hd).filter (inPortBit w)).length_eq
  have hB_perm : (V.filter (outPortBit w)).length = ((classPhases2 P w t r).filter (outPortBit w)).length :=
    ((rankedClassPhases_perm hd).filter (outPortBit w)).length_eq
  rw [hA_perm] at hL14_in
  rw [hB_perm] at hL14_out
  rw [rankSum_rankedClassPhases hd (inPortBit w)] at hL14_in
  rw [rankSum_rankedClassPhases hd (outPortBit w)] at hL14_out
  by_cases ht : t % 2 = 0
  · have hA_eq : ((classPhases2 P w t r).filter (inPortBit w)).length = nCnt P w (t - 1) r := by
      have h1 : (classPhases2 P w t r).filter (inPortBit w) =
          (classPhases2 P w t r).filter (fun i => decide (inDir w i = .north)) := by
        apply List.filter_congr; intro i hi
        unfold inPortBit; rw [(mem_classPhases2.mp hi).2.1, ite_eq_left ht]
      rw [h1]
      have hna := depCount_eq_arrCount_north h.1 hd (t - 1) r
      rw [show t - 1 + 1 = t by omega] at hna
      exact hna.symm
    have hB_eq : ((classPhases2 P w t r).filter (outPortBit w)).length = eCnt P w t r := by
      have h1 : (classPhases2 P w t r).filter (outPortBit w) =
          (classPhases2 P w t r).filter (fun i => decide (outDir w i = .east)) := by
        apply List.filter_congr; intro i hi
        unfold outPortBit; rw [(mem_classPhases2.mp hi).2.1, ite_eq_left ht]
      rw [h1]; rfl
    have hpos_par : (nCnt P w (t - 1) r + eCnt P w t r) % 2 = posPortPar P w t r := by
      have hna := depCount_eq_arrCount_north h.1 hd (t - 1) r
      rw [show t - 1 + 1 = t by omega] at hna
      unfold posPortPar; rw [ite_eq_left ht, ← hna]
    have hlin : (nCnt P w (t - 1) r * (classMult P w t r - 1) +
        eCnt P w t r * (classMult P w t r - 1)) % 2 = localCorr P w t r := by
      have hp_mod : posPortPar P w t r % 2 = posPortPar P w t r := by
        unfold posPortPar; rw [ite_eq_left ht]; exact Nat.mod_mod _ 2
      have hmul : ((nCnt P w (t - 1) r + eCnt P w t r) * (classMult P w t r - 1)) % 2 =
          (posPortPar P w t r * (classMult P w t r - 1)) % 2 := by
        rw [Nat.mul_mod _ _ 2, Nat.mul_mod (posPortPar P w t r) _ 2, hpos_par, hp_mod]
      rw [← Nat.add_mul, hmul]
      exact even_layer_localCorr_eq h hd ht r
    have hxor :
        ((((classPhases2 P w t r).filter (inPortBit w)).map (Drift.stableRank P w)).sum +
        (((classPhases2 P w t r).filter (outPortBit w)).map (Drift.stableRank P w)).sum) % 2 =
        localLeftRankSum P w t r % 2 := by
      have hx := sum_filter_xor_mod_two (inPortBit w) (outPortBit w) (Drift.stableRank P w)
        (classPhases2 P w t r)
      have hf : (classPhases2 P w t r).filter (fun i => xor (inPortBit w i) (outPortBit w i)) =
          (classPhases2 P w t r).filter (fun i => w i) := by
        apply List.filter_congr; intro i hi
        unfold inPortBit outPortBit
        simp only [(mem_classPhases2.mp hi).2.1, ht, ite_true]
        exact (even_layer_left_iff_xor ht hi).symm
      rw [hf] at hx
      exact hx.symm
    unfold inPairCount outPairCount
    rw [ite_eq_left ht, ite_eq_left ht]
    rw [hA_eq] at hL14_in
    rw [hB_eq] at hL14_out
    dsimp only [V] at hL14_in hL14_out
    omega
  · have hodd : t % 2 = 1 := by omega
    have hA_eq : ((classPhases2 P w t r).filter (inPortBit w)).length = eCnt P w (t - 1) (!r) := by
      have h1 : (classPhases2 P w t r).filter (inPortBit w) =
          (classPhases2 P w t r).filter (fun i => decide (inDir w i = .east)) := by
        apply List.filter_congr; intro i hi
        unfold inPortBit; rw [(mem_classPhases2.mp hi).2.1, ite_eq_right ht]
      rw [h1]
      have hea := depCount_eq_arrCount_east h.1 hd (t - 1) (!r)
      rw [show t - 1 + 1 = t by omega, Bool.not_not] at hea
      exact hea.symm
    have hB_eq : ((classPhases2 P w t r).filter (outPortBit w)).length = nCnt P w t r := by
      have h1 : (classPhases2 P w t r).filter (outPortBit w) =
          (classPhases2 P w t r).filter (fun i => decide (outDir w i = .north)) := by
        apply List.filter_congr; intro i hi
        unfold outPortBit; rw [(mem_classPhases2.mp hi).2.1, ite_eq_right ht]
      rw [h1]; rfl
    have hpos_par : (eCnt P w (t - 1) (!r) + nCnt P w t r) % 2 = posPortPar P w t r := by
      have hea := depCount_eq_arrCount_east h.1 hd (t - 1) (!r)
      rw [show t - 1 + 1 = t by omega, Bool.not_not] at hea
      unfold posPortPar; rw [ite_eq_right ht, ← hea]
    have hsum_all :
        localLeftRankSum P w t r +
          (((classPhases2 P w t r).filter (fun i => !w i)).map (Drift.stableRank P w)).sum =
        classMult P w t r * (classMult P w t r - 1) / 2 := by
      unfold localLeftRankSum
      rw [sum_filter_add_not (fun i => w i) (Drift.stableRank P w) (classPhases2 P w t r)]
      unfold classMult classPhases2
      have hperm := Drift.stableRank_map_perm_range (v := (2, -2)) (c := classRep t r) hd
        drift_two_negTwo_ne_zero
      rw [PortInversion.perm_sum hperm, sum_range_eq_pairCount, PortInversion.pairCount_eq_div]
    have hxor :
        ((((classPhases2 P w t r).filter (inPortBit w)).map (Drift.stableRank P w)).sum +
        (((classPhases2 P w t r).filter (outPortBit w)).map (Drift.stableRank P w)).sum) % 2 =
        (((classPhases2 P w t r).filter (fun i => !w i)).map (Drift.stableRank P w)).sum % 2 := by
      have hx := sum_filter_xor_mod_two (inPortBit w) (outPortBit w) (Drift.stableRank P w)
        (classPhases2 P w t r)
      have hf : (classPhases2 P w t r).filter (fun i => xor (inPortBit w i) (outPortBit w i)) =
          (classPhases2 P w t r).filter (fun i => !w i) := by
        apply List.filter_congr; intro i hi
        unfold inPortBit outPortBit
        simp only [(mem_classPhases2.mp hi).2.1, ht, ite_false]
        exact (odd_layer_right_iff_xor hodd hi).symm
      rw [hf] at hx
      exact hx.symm
    have hlin : (classMult P w t r * (classMult P w t r - 1) / 2 +
        (eCnt P w (t - 1) (!r) + nCnt P w t r) * (classMult P w t r - 1)) % 2 =
        localCorr P w t r := by
      have hp_mod : posPortPar P w t r % 2 = posPortPar P w t r := by
        unfold posPortPar; rw [ite_eq_right ht]; exact Nat.mod_mod _ 2
      have hmul : ((eCnt P w (t - 1) (!r) + nCnt P w t r) * (classMult P w t r - 1)) % 2 =
          (posPortPar P w t r * (classMult P w t r - 1)) % 2 := by
        rw [Nat.mul_mod _ _ 2, Nat.mul_mod (posPortPar P w t r) _ 2, hpos_par, hp_mod]
      have hloc := odd_layer_localCorr_eq h hd hodd r
      omega
    unfold inPairCount outPairCount
    rw [ite_eq_right ht, ite_eq_right ht]
    rw [hA_eq] at hL14_in
    rw [hB_eq] at hL14_out
    have hmul_dist : (eCnt P w (t - 1) (!r) + nCnt P w t r) * (classMult P w t r - 1) =
        eCnt P w (t - 1) (!r) * (classMult P w t r - 1) + nCnt P w t r * (classMult P w t r - 1) :=
      Nat.add_mul _ _ _
    dsimp only [V] at hL14_in hL14_out
    omega

private theorem pairCount_window_sum_even {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    let j0 := botLayer P w
    let m := (layerWidth P w / 2).toNat
    ((windowVertices j0 m).map (fun v => inPairCount P w v.1 v.2 + outPairCount P w v.1 v.2)).sum % 2 = 0 := by
  intro j0 m
  let inL : Int → Nat := fun t => inPairCount P w t false + inPairCount P w t true
  let outL : Int → Nat := fun t => outPairCount P w t false + outPairCount P w t true
  have hshift : ∀ t : Int, inL (t + 1) = outL t := by
    intro t
    dsimp [inL, outL, inPairCount, outPairCount]
    by_cases ht : t % 2 = 0
    · have hne : (t + 1) % 2 ≠ 0 := by omega
      simp only [ht, ite_true, hne, ite_false, Bool.not_false, Bool.not_true,
        show t + 1 - 1 = t by omega]; omega
    · have hev : (t + 1) % 2 = 0 := by omega
      simp only [ht, ite_false, hev, ite_true, show t + 1 - 1 = t by omega]
  have hbot0 : inL j0 = 0 := by
    have hne : j0 % 2 ≠ 0 := by have := botLayer_odd h hd; omega
    dsimp [inL, inPairCount]
    simp only [hne, ite_false, Bool.not_false, Bool.not_true]
    have h1 : eCnt P w (j0 - 1) true = 0 := depCount_eq_zero_of_lt_bot true .east (by omega)
    have h2 : eCnt P w (j0 - 1) false = 0 := depCount_eq_zero_of_lt_bot false .east (by omega)
    rw [h1, h2]; rfl
  have htop0 : outL (j0 + (2 * m : Int)) = 0 := by
    have htop_eq : j0 + (2 * m : Int) = topLayer P w := by
      have ht := topLayer_odd h hd
      have hb := botLayer_odd h hd
      have hw := layerWidth_ge_two h hd
      dsimp [j0, m]; unfold layerWidth at hw ⊢; omega
    rw [htop_eq]
    have hne : topLayer P w % 2 ≠ 0 := by have := topLayer_odd h hd; omega
    dsimp [outL, outPairCount]
    simp only [hne, ite_false]
    rw [nCnt_topLayer_eq_zero h hd false, nCnt_topLayer_eq_zero h hd true]; rfl
  have hsum_eq :
      ((windowLayers j0 m).map inL).sum = ((windowLayers j0 m).map outL).sum := by
    unfold windowLayers
    rw [List.map_map, List.map_map]
    have h1 :
        ((List.range (2 * m + 1)).map (fun k : Nat => inL (j0 + (k : Int)))).sum =
        inL j0 + ((List.range (2 * m)).map (fun k : Nat => outL (j0 + (k : Int)))).sum := by
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      simp only [Int.natCast_zero, Int.add_zero]
      congr 1; congr 1
      apply List.map_congr_left
      intro k _
      have heq : j0 + ((k + 1 : Nat) : Int) = (j0 + (k : Int)) + 1 := by omega
      simp only [Function.comp_def, heq, hshift]
    have h2 :
        ((List.range (2 * m + 1)).map (fun k : Nat => outL (j0 + (k : Int)))).sum =
        ((List.range (2 * m)).map (fun k : Nat => outL (j0 + (k : Int)))).sum +
          outL (j0 + ((2 * m : Nat) : Int)) := by
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    change ((List.range (2 * m + 1)).map (fun k : Nat => inL (j0 + (k : Int)))).sum =
      ((List.range (2 * m + 1)).map (fun k : Nat => outL (j0 + (k : Int)))).sum
    rw [h1, h2, hbot0]
    have htop0' : outL (j0 + ((2 * m : Nat) : Int)) = 0 := by simpa using htop0
    rw [htop0']; omega
  have hflat : ∀ (ts : List Int) (f : Int × Bool → Nat),
      ((ts.flatMap (fun t => [(t, false), (t, true)])).map f).sum =
      (ts.map (fun t => f (t, false) + f (t, true))).sum := by
    intro ts f
    induction ts with
    | nil => rfl
    | cons t ts its =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, its]; omega
  unfold windowVertices
  rw [hflat]
  have hsplit : ∀ ts : List Int,
      (ts.map (fun t => (inPairCount P w t false + outPairCount P w t false) +
        (inPairCount P w t true + outPairCount P w t true))).sum =
      (ts.map inL).sum + (ts.map outL).sum := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts its => simp only [List.map_cons, List.sum_cons, inL, outL] at its ⊢; omega
  rw [hsplit, hsum_eq]; omega

private theorem sum_localLeftRankSum_eq {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    let j0 := botLayer P w
    let m := (layerWidth P w / 2).toNat
    ((windowVertices j0 m).map (fun v => localLeftRankSum P w v.1 v.2)).sum = leftRankSum P w := by
  intro j0 m
  have hperm := vblocks_flatten_perm_range h hd
  have h1 : (((windowVertices j0 m).map (fun v => rankedClassPhases P w v.1 v.2)).flatten.filter
      (fun i => w i)).Perm ((List.range P).filter (fun i => w i)) := hperm.filter _
  unfold leftRankSum
  rw [← PortInversion.perm_sum (h1.map (Drift.stableRank P w))]
  have hflat_filter : ∀ bs : List (List Nat),
      ((bs.flatten.filter (fun i => w i)).map (Drift.stableRank P w)).sum =
      (bs.map (fun b => ((b.filter (fun i => w i)).map (Drift.stableRank P w)).sum)).sum := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs ibs =>
      simp only [List.flatten_cons, List.filter_append, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ibs]
  rw [hflat_filter, List.map_map]
  congr 1; apply List.map_congr_left
  intro v _
  exact (PortInversion.perm_sum (((rankedClassPhases_perm hd).filter (fun i => w i)).map
    (Drift.stableRank P w))).symm

/-- **L23 (general `(2, -2)` parity identity, valid for every growth `g`):**
`leftRankSum P w ≡ 1 + E + totalLocalCorr (mod 2)`. -/
theorem leftRankSum_parity_general {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) :
    let j0 := botLayer P w
    let m := (layerWidth P w / 2).toNat
    (leftRankSum P w + 1 +
      pairInvSum edgeSrcLt edgeDstLt (edgeMult P w) (gadgetStack j0 m) +
      ((windowLayers j0 m).map (fun t => localCorr P w t false + localCorr P w t true)).sum) % 2 = 0 := by
  intro j0 m
  have hL16 := portWord_inversions_parity h hd
  have hpc := pairCount_window_sum_even h hd
  have hleft := sum_localLeftRankSum_eq h hd
  have hsum_vtx :
      ((windowVertices j0 m).map (fun v =>
        PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (inPortBit w)) +
        PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (outPortBit w)) +
        localLeftRankSum P w v.1 v.2 + localCorr P w v.1 v.2 +
        (inPairCount P w v.1 v.2 + outPairCount P w v.1 v.2))).sum % 2 = 0 := by
    have h0 : ∀ (xs : List (Int × Bool)) (f : Int × Bool → Nat),
        (∀ x ∈ xs, f x % 2 = 0) → (xs.map f).sum % 2 = 0 := by
      intro xs f hf
      induction xs with
      | nil => rfl
      | cons x xs ixs =>
        simp only [List.map_cons, List.sum_cons]
        have hx := hf x (by simp)
        have hxs := ixs (fun y hy => hf y (by simp [hy]))
        omega
    apply h0
    intro v _
    have hv := vertex_portWord_parity h hd v.1 v.2
    omega
  have hsplit : ∀ (xs : List (Int × Bool)) (f1 f2 f3 f4 : Int × Bool → Nat),
      (xs.map (fun v => f1 v + f2 v + f3 v + f4 v)).sum =
      (xs.map f1).sum + (xs.map f2).sum + (xs.map f3).sum + (xs.map f4).sum := by
    intro xs f1 f2 f3 f4
    induction xs with
    | nil => rfl
    | cons x xs ixs => simp only [List.map_cons, List.sum_cons]; omega
  have hloc_eq :
      ((windowVertices j0 m).map (fun v => localCorr P w v.1 v.2)).sum =
      ((windowLayers j0 m).map (fun t => localCorr P w t false + localCorr P w t true)).sum := by
    unfold windowVertices
    induction windowLayers j0 m with
    | nil => rfl
    | cons t ts its =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil, its]; omega
  rw [hsplit (windowVertices j0 m)
    (fun v => PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (inPortBit w)) +
      PortInversion.wordInv ((rankedClassPhases P w v.1 v.2).map (outPortBit w)))
    (fun v => localLeftRankSum P w v.1 v.2)
    (fun v => localCorr P w v.1 v.2)
    (fun v => inPairCount P w v.1 v.2 + outPairCount P w v.1 v.2)] at hsum_vtx
  rw [hleft, hloc_eq] at hsum_vtx
  dsimp only [j0, m] at hsum_vtx ⊢
  omega

/-- **L23 (under `PureOddWake`, part 1):** `leftRankSum P w % 2 = (1 + E) % 2`. -/
theorem pureOdd_leftRankSum_parity {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) :
    leftRankSum P w % 2 =
      (1 + pairInvSum edgeSrcLt edgeDstLt (edgeMult P w)
        (gadgetStack (botLayer P w) (layerWidth P w / 2).toNat)) % 2 := by
  have hgen := leftRankSum_parity_general h hd
  have hloc := pureOdd_total_localCorr_zero h hd hpure
    (windowLayers (botLayer P w) (layerWidth P w / 2).toNat)
  omega

/-- **L23 (under `PureOddWake`, part 2):** The edge-block inversion parity `E % 2` equals the
two-lane chain parity `∑_{j, r} (n_{j, r} + n_{j, r} · n_{j+2, r}) % 2`. -/
theorem pureOdd_edgeCross_eq_chain {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hpure : PureOddWake P w) :
    pairInvSum edgeSrcLt edgeDstLt (edgeMult P w)
      (gadgetStack (botLayer P w) (layerWidth P w / 2).toNat) % 2 =
    (((oddLayers P w).map (fun j =>
      nCnt P w j false % 2 + (nCnt P w j false % 2) * (nCnt P w (j + 2) false % 2))).sum +
     ((oddLayers P w).map (fun j =>
      nCnt P w j true % 2 + (nCnt P w j true % 2) * (nCnt P w (j + 2) true % 2))).sum) % 2 := by
  let j0 := botLayer P w
  let m := (layerWidth P w / 2).toNat
  have hj0_odd : j0 % 2 = 1 := botLayer_odd h hd
  have htop_eq : j0 + 2 * (m : Int) = topLayer P w := by
    have ht := topLayer_odd h hd
    have hw := layerWidth_ge_two h hd
    dsimp [j0, m]; unfold layerWidth at hw ⊢; omega
  have hwt_mod : ∀ e ∈ gadgetStack j0 m, edgeMult P w e % 2 = nCnt P w e.j e.r % 2 := by
    intro e he
    have hodd : e.j % 2 = 1 := ((mem_gadgetStack_iff hj0_odd).mp he).1
    rcases e with ⟨j, r, k⟩
    dsimp only at hodd
    cases k
    · rfl
    · simpa [edgeMult, GEdge.srcLayer, GEdge.srcLane, GEdge.dir, Bool.not_not] using
        pureOdd_wCnt_mod_two h hd hpure (show (j + 1) % 2 = 0 by omega) (!r)
    · simpa [edgeMult, GEdge.srcLayer, GEdge.srcLane, GEdge.dir, Bool.not_not] using
        pureOdd_eCnt_mod_two h hd hpure (show (j + 1) % 2 = 0 by omega) (!r)
    · simpa [edgeMult, GEdge.srcLayer, GEdge.srcLane, GEdge.dir, show j + 2 - 2 = j by omega] using
        pureOdd_sCnt_mod_two h hd hpure (show (j + 2) % 2 = 1 by omega) r
  rw [pairInvSum_mod_two_congr edgeSrcLt edgeDstLt (edgeMult P w)
    (fun e => nCnt P w e.j e.r % 2) (gadgetStack j0 m) (fun e he => by rw [hwt_mod e he, Nat.mod_mod])]
  rw [gadgetStack_pairInvSum_mod_two (fun j r => nCnt P w j r % 2) j0 m (by
    rw [htop_eq, nCnt_topLayer_eq_zero h hd false, nCnt_topLayer_eq_zero h hd true]; exact ⟨rfl, rfl⟩)]
  have hodd_split : ∀ r : Bool,
      ((oddLayers P w).map (fun j =>
        nCnt P w j r % 2 + (nCnt P w j r % 2) * (nCnt P w (j + 2) r % 2))).sum =
      ((List.range m).map (fun k : Nat =>
        let j := j0 + 2 * (k : Int)
        nCnt P w j r % 2 + (nCnt P w j r % 2) * (nCnt P w (j + 2) r % 2))).sum := by
    intro r
    unfold oddLayers
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.map_map]
    simp only [List.map_singleton, List.sum_singleton]
    have hlast : botLayer P w + 2 * ((m : Nat) : Int) = topLayer P w := htop_eq
    change ((List.range m).map (fun k : Nat =>
        let j := j0 + 2 * (k : Int)
        nCnt P w j r % 2 + (nCnt P w j r % 2) * (nCnt P w (j + 2) r % 2))).sum +
      (nCnt P w (botLayer P w + 2 * ((m : Nat) : Int)) r % 2 +
        (nCnt P w (botLayer P w + 2 * ((m : Nat) : Int)) r % 2) *
          (nCnt P w (botLayer P w + 2 * ((m : Nat) : Int) + 2) r % 2)) = _
    rw [hlast, nCnt_topLayer_eq_zero h hd r]
    simp
  rw [hodd_split false, hodd_split true]

end TwoCellDiagonal
end LangtonsAnt
