import PersistA.FirstVisitMap
import PersistA.FiniteOrbitCycle
import PersistA.TwoLaneCycle

namespace LangtonsAnt.PersistA.FirstVisitCycle

open FirstVisitMap FiniteOrbitCycle

theorem exists_rank_zero_cycle {v : Point} {P : Nat} {w : Nat → Bool}
    (hP : 0 < P) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    ∃ n : Nat, ∃ hn : 0 < n, ∃ c : Fin n → Nat,
      Function.Injective c ∧ (∀ i, c i < P ∧ Drift.stableRank P w (c i) = 0) ∧
      (∀ i, firstPred v P w (c i) = c ⟨(i.val+1)%n, Nat.mod_lt _ hn⟩) := by
  let xs := (List.range P).filter (fun i => decide (Drift.stableRank P w i = 0))
  have hmem : ∀ i, i ∈ xs ↔ i < P ∧ Drift.stableRank P w i = 0 := by
    intro i
    simp [xs]
  have hfirst := firstOf_spec hd hv hP
  have ha : firstOf v P w 0 ∈ xs := (hmem _).mpr
    ⟨(Drift.mem_classPhases.mp hfirst.1).1,hfirst.2⟩
  have hf : ∀ i ∈ xs, firstPred v P w i ∈ xs := by
    intro i hi
    have hs := firstPred_spec hd hv ((hmem i).mp hi).1
    exact (hmem _).mpr ⟨hs.1,hs.2.1⟩
  obtain ⟨n,hn,c,hinj,hc,hstep⟩ := exists_simple_cycle xs (firstPred v P w) hf ha
  exact ⟨n,hn,c,hinj,(fun i => (hmem _).mp (hc i)),hstep⟩

def key (w : Nat → Bool) (i : Nat) : Int × Int :=
  (layer (wordPos w i), (wordPos w i).1 % 2)

theorem key_injective_on_rank_zero {P i j : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, -2)) (hi : i < P) (hj : j < P)
    (hri : Drift.stableRank P w i = 0) (hrj : Drift.stableRank P w j = 0)
    (he : key w i = key w j) : i = j := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0, 0) := by decide
  have hc : Drift.SameClass (2, -2) (wordPos w i) (wordPos w j) := by
    apply (DiagonalMultipleLanes.sameClass_diagDrift_iff (m := 2) (by decide) _ _).mpr
    exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  exact Drift.stableRank_injective_on_class hd hv
    (Drift.mem_classPhases.mpr ⟨hi,hc⟩)
    (Drift.mem_classPhases.mpr ⟨hj,Drift.SameClass.refl _ _⟩) (hri.trans hrj.symm)


theorem firstPred_edge {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2, -2)) (hi : i < P) :
    TwoLaneCycle.Edge (key w (firstPred (2, -2) P w i)) (key w i) := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0, 0) := by decide
  have hclass := firstPred_class_edge hw hd hv hi
  have he := (DiagonalMultipleLanes.sameClass_diagDrift_iff (m := 2) (by decide) _ _).mp hclass
  have haxis := inDir_horizontal_iff w i
  change ((Drift.inDir w i).horizontal = true ↔ layer (wordPos w i) % 2 = 1) at haxis
  unfold TwoLaneCycle.Edge key
  cases hdirection : Drift.inDir w i <;>
    simp [hdirection, move, layer, weight, Direction.horizontal] at he haxis <;>
    dsimp [layer, weight]
  all_goals
    by_cases hs : ((wordPos w (firstPred (2, -2) P w i)).1 +
      (wordPos w (firstPred (2, -2) P w i)).2) % 2 = 0
    · simp only [hs, ite_true]
      omega
    · simp only [hs, ite_false]
      omega


theorem exists_rank_zero_four_return {P : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hP : 0 < P) (hd : wordDrift P w = (2, -2)) :
    ∃ i, i < P ∧ Drift.stableRank P w i = 0 ∧
      firstPred (2, -2) P w (firstPred (2, -2) P w
        (firstPred (2, -2) P w (firstPred (2, -2) P w i))) = i := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0, 0) := by decide
  obtain ⟨n,hn,c,hinj,hc,hstep⟩ := exists_rank_zero_cycle hP hd hv
  have hcoord : Function.Injective (fun i => key w (c i)) := by
    intro i j he
    exact hinj (key_injective_on_rank_zero hd (hc i).1 (hc j).1 (hc i).2 (hc j).2 he)
  have hstep' : ∀ i, firstPred (2, -2) P w (c i) = c (TwoLaneCycle.nextIndex hn i) := by
    intro i
    rw [TwoLaneCycle.nextIndex_mod]
    exact hstep i
  have hedge : ∀ i, TwoLaneCycle.Edge (key w (c (TwoLaneCycle.nextIndex hn i))) (key w (c i)) := by
    intro i
    rw [← hstep']
    exact firstPred_edge hw hd (hc i).1
  obtain ⟨q,hfour⟩ := TwoLaneCycle.finite_reverse_cycle_four hn (fun i => key w (c i)) hcoord hedge
  have hforward : TwoLaneCycle.nextIndex hn (TwoLaneCycle.nextIndex hn
      (TwoLaneCycle.nextIndex hn (TwoLaneCycle.nextIndex hn q))) = q := by
    have he := congrArg (fun i => TwoLaneCycle.nextIndex hn (TwoLaneCycle.nextIndex hn
      (TwoLaneCycle.nextIndex hn (TwoLaneCycle.nextIndex hn i)))) hfour
    simpa only [TwoLaneCycle.next_prev_index] using he.symm
  refine ⟨c q,(hc q).1,(hc q).2,?_⟩
  rw [hstep',hstep',hstep',hstep',hforward]


def dx (d : Direction) : Int := (move (0,0) d).1

def dy (d : Direction) : Int := (move (0,0) d).2

theorem liftStep_residue {p q : Point} {d : Direction}
    (hc : Drift.SameClass (2,-2) (move p d) q) :
    2 * Drift.liftStep (2,-2) p d = p.1 % 2 + dx d - q.1 % 2 := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0,0) := by decide
  have hm := Drift.lift_move hv p d
  have he := (DiagonalMultipleLanes.sameClass_diagDrift_iff (m := 2) (by decide) _ _).mp hc
  cases d <;> simp only [Drift.lift, dx, move] at hm he ⊢ <;> omega

theorem four_clock_positive {P : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2,-2))
    {i0 i1 i2 i3 : Nat} (h0 : i0<P) (h1 : i1<P) (h2 : i2<P) (h3 : i3<P)
    (e0 : firstPred (2,-2) P w i0=i1) (e1 : firstPred (2,-2) P w i1=i2)
    (e2 : firstPred (2,-2) P w i2=i3) (e3 : firstPred (2,-2) P w i3=i0) :
    0 < Drift.liftStep (2,-2) (wordPos w i1) (Drift.inDir w i0) +
      Drift.liftStep (2,-2) (wordPos w i2) (Drift.inDir w i1) +
      Drift.liftStep (2,-2) (wordPos w i3) (Drift.inDir w i2) +
      Drift.liftStep (2,-2) (wordPos w i0) (Drift.inDir w i3) := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0,0) := by decide
  have hc0 := firstPred_clock hw hd hv h0
  have hc1 := firstPred_clock hw hd hv h1
  have hc2 := firstPred_clock hw hd hv h2
  have hc3 := firstPred_clock hw hd hv h3
  rw [e0] at hc0
  rw [e1] at hc1
  rw [e2] at hc2
  rw [e3] at hc3
  apply Classical.byContradiction
  intro hn
  have hprod := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (P : Int) by omega)
    (show Drift.liftStep (2,-2) (wordPos w i1) (Drift.inDir w i0) +
      Drift.liftStep (2,-2) (wordPos w i2) (Drift.inDir w i1) +
      Drift.liftStep (2,-2) (wordPos w i3) (Drift.inDir w i2) +
      Drift.liftStep (2,-2) (wordPos w i0) (Drift.inDir w i3) ≤ 0 by omega)
  simp only [Int.mul_add] at hprod
  omega


theorem layer_edge {p q : Point} {d : Direction}
    (hc : Drift.SameClass (2,-2) (move p d) q) :
    layer q = layer p + dx d + dy d := by
  have he := (DiagonalMultipleLanes.sameClass_diagDrift_iff (m := 2) (by decide) _ _).mp hc
  cases d <;> simp only [layer,weight,move,dx,dy] at he ⊢ <;> omega

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem four_direction_classification {t0 t1 t2 t3 : Int} {d0 d1 d2 d3 : Direction}
    (e0 : t0=t1+dx d0+dy d0) (e1 : t1=t2+dx d1+dy d1)
    (e2 : t2=t3+dx d2+dy d2) (e3 : t3=t0+dx d3+dy d3)
    (h0 : d0.horizontal=true ↔ t0%2=1) (h1 : d1.horizontal=true ↔ t1%2=1)
    (h2 : d2.horizontal=true ↔ t2%2=1) (h3 : d3.horizontal=true ↔ t3%2=1)
    (hpos : 0<dx d0+dx d1+dx d2+dx d3) :
    (d0=.east ∧ d1=.south ∧ d2=.east ∧ d3=.south) ∨
    (d0=.south ∧ d1=.east ∧ d2=.south ∧ d3=.east) := by
  cases d0 <;> cases d1 <;> cases d2 <;> cases d3 <;>
    simp only [dx,dy,move] at e0 e1 e2 e3 <;>
    simp [dx,move,Direction.horizontal] at h0 h1 h2 h3 hpos
  all_goals first | exact Or.inl ⟨rfl,rfl,rfl,rfl⟩ | exact Or.inr ⟨rfl,rfl,rfl,rfl⟩ | omega

theorem firstPred_four_directions {P : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2,-2))
    {i0 i1 i2 i3 : Nat} (h0 : i0<P) (h1 : i1<P) (h2 : i2<P) (h3 : i3<P)
    (e0 : firstPred (2,-2) P w i0=i1) (e1 : firstPred (2,-2) P w i1=i2)
    (e2 : firstPred (2,-2) P w i2=i3) (e3 : firstPred (2,-2) P w i3=i0) :
    (Drift.inDir w i0=.east ∧ Drift.inDir w i1=.south ∧
      Drift.inDir w i2=.east ∧ Drift.inDir w i3=.south) ∨
    (Drift.inDir w i0=.south ∧ Drift.inDir w i1=.east ∧
      Drift.inDir w i2=.south ∧ Drift.inDir w i3=.east) := by
  have hv : ((2 : Int), (-2 : Int)) ≠ (0,0) := by decide
  have c0 := firstPred_class_edge hw hd hv h0
  have c1 := firstPred_class_edge hw hd hv h1
  have c2 := firstPred_class_edge hw hd hv h2
  have c3 := firstPred_class_edge hw hd hv h3
  rw [e0] at c0
  rw [e1] at c1
  rw [e2] at c2
  rw [e3] at c3
  have v0 := liftStep_residue c0
  have v1 := liftStep_residue c1
  have v2 := liftStep_residue c2
  have v3 := liftStep_residue c3
  have hpos := four_clock_positive hw hd h0 h1 h2 h3 e0 e1 e2 e3
  exact four_direction_classification (layer_edge c0) (layer_edge c1) (layer_edge c2) (layer_edge c3)
    (inDir_horizontal_iff w i0) (inDir_horizontal_iff w i1)
    (inDir_horizontal_iff w i2) (inDir_horizontal_iff w i3) (by omega)


structure Core (P : Nat) (w : Nat → Bool) where
  a0 : Nat
  b1 : Nat
  a1 : Nat
  b0 : Nat
  a0_lt : a0<P
  b1_lt : b1<P
  a1_lt : a1<P
  b0_lt : b0<P
  a0_rank : Drift.stableRank P w a0=0
  b1_rank : Drift.stableRank P w b1=0
  a1_rank : Drift.stableRank P w a1=0
  b0_rank : Drift.stableRank P w b0=0
  edge0 : firstPred (2,-2) P w a0=b1
  edge1 : firstPred (2,-2) P w b1=a1
  edge2 : firstPred (2,-2) P w a1=b0
  edge3 : firstPred (2,-2) P w b0=a0
  dir0 : Drift.inDir w a0=.south
  dir1 : Drift.inDir w b1=.east
  dir2 : Drift.inDir w a1=.south
  dir3 : Drift.inDir w b0=.east

theorem exists_core {P : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hP : 0<P) (hd : wordDrift P w=(2,-2)) :
    Nonempty (Core P w) := by
  have hv : ((2 : Int),(-2 : Int)) ≠ (0,0) := by decide
  obtain ⟨i,h0,r0,hfour⟩ := exists_rank_zero_four_return hw hP hd
  let f := firstPred (2,-2) P w
  have h1 := firstPred_spec hd hv h0
  have h2 := firstPred_spec hd hv h1.1
  have h3 := firstPred_spec hd hv h2.1
  have h4 := firstPred_four_directions hw hd h0 h1.1 h2.1 h3.1 rfl rfl rfl hfour
  rcases h4 with h4 | h4
  · refine ⟨⟨f i,f (f i),f (f (f i)),i,h1.1,h2.1,h3.1,h0,
      h1.2.1,h2.2.1,h3.2.1,r0,rfl,rfl,hfour,rfl,?_,?_,?_,?_⟩⟩
    · exact h4.2.1
    · exact h4.2.2.1
    · exact h4.2.2.2
    · exact h4.1
  · exact ⟨⟨i,f i,f (f i),f (f (f i)),h0,h1.1,h2.1,h3.1,
      r0,h1.2.1,h2.2.1,h3.2.1,rfl,rfl,rfl,hfour,
      h4.1,h4.2.1,h4.2.2.1,h4.2.2.2⟩⟩


end LangtonsAnt.PersistA.FirstVisitCycle
