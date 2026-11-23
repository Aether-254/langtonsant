import PersistA.FirstVisitCycle
import PersistA.GatePath

namespace LangtonsAnt.PersistA.TwoGateDecomposition

open FirstVisitMap FirstVisitCycle GatePath

theorem rank_zero_outDir {P i : Nat} {w : Nat → Bool} (hw : ConsistentWord P w)
    (hi : i<P) (hr : Drift.stableRank P w i=0) :
    Drift.outDir w i=(Drift.inDir w i).right := by
  have hc : w i=false := by rw [Drift.consistentWord_stableRank_color hw hi,hr]; rfl
  change turn (w i) (Drift.inDir w i) = _
  rw [hc]
  rfl

theorem liftStep_south (p : Point) : Drift.liftStep (2,-2) p .south=0 := by
  have he := liftStep_residue (d := .south) (Drift.SameClass.refl (2,-2) (move p .south))
  simp only [dx,move] at he
  omega

theorem core_outgoing {P : Nat} {w : Nat → Bool} (hw : ConsistentWord P w) (c : Core P w) :
    Drift.outDir w c.a0=.west ∧ Drift.outDir w c.b1=.south ∧
    Drift.outDir w c.a1=.west ∧ Drift.outDir w c.b0=.south := by
  rw [rank_zero_outDir hw c.a0_lt c.a0_rank,rank_zero_outDir hw c.b1_lt c.b1_rank,
    rank_zero_outDir hw c.a1_lt c.a1_rank,rank_zero_outDir hw c.b0_lt c.b0_rank,
    c.dir0,c.dir1,c.dir2,c.dir3]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem core_bridges {P : Nat} {w : Nat → Bool} (hw : ConsistentWord P w)
    (hd : wordDrift P w=(2,-2)) (c : Core P w) :
    Drift.succ P c.b0=c.a1 ∧ Drift.succ P c.b1=c.a0 := by
  have hv : ((2 : Int),(-2 : Int)) ≠ (0,0) := by decide
  have hout := core_outgoing hw c
  constructor
  · exact zero_port_successor hw hd hv c.b0_lt c.a1_lt c.a1_rank c.edge2
      (hout.2.2.2.trans c.dir2.symm)
  · exact zero_port_successor hw hd hv c.b1_lt c.a0_lt c.a0_rank c.edge0
      (hout.2.1.trans c.dir0.symm)

theorem core_exit_data {P : Nat} {w : Nat → Bool} (hw : ConsistentWord P w)
    (hd : wordDrift P w=(2,-2)) (c : Core P w) :
    Drift.SameClass (2,-2) (wordPos w (Drift.pred P c.b0)) (wordPos w c.a0) ∧
    Drift.SameClass (2,-2) (wordPos w (Drift.pred P c.b1)) (wordPos w c.a1) ∧
    Drift.outDir w (Drift.pred P c.b0)=.east ∧ Drift.outDir w (Drift.pred P c.b1)=.east ∧
    Drift.stableTime (2,-2) P w c.a0 < Drift.stableTime (2,-2) P w (Drift.pred P c.b0) ∧
    Drift.stableTime (2,-2) P w c.a1 < Drift.stableTime (2,-2) P w (Drift.pred P c.b1) := by
  have hv : ((2 : Int),(-2 : Int)) ≠ (0,0) := by decide
  have h0 := firstPred_spec hd hv c.b0_lt
  have h1 := firstPred_spec hd hv c.b1_lt
  rw [c.edge3] at h0
  rw [c.edge1] at h1
  have he0 : Drift.pred P c.b0<P := UnitDiagonalMatching.pred_lt c.b0_lt
  have he1 : Drift.pred P c.b1<P := UnitDiagonalMatching.pred_lt c.b1_lt
  have d0 := Drift.successor_heading hw.1 he0
  have d1 := Drift.successor_heading hw.1 he1
  have s0 : Drift.succ P (Drift.pred P c.b0)=c.b0 := UnitDiagonalMatching.succ_pred c.b0_lt
  have s1 : Drift.succ P (Drift.pred P c.b1)=c.b1 := UnitDiagonalMatching.succ_pred c.b1_lt
  rw [s0,c.dir3] at d0
  rw [s1,c.dir1] at d1
  have l0 := rank_zero_time_le hd hv c.a0_lt he0 c.a0_rank h0.2.2
  have l1 := rank_zero_time_le hd hv c.a1_lt he1 c.a1_rank h1.2.2
  have outs := core_outgoing hw c
  have n0 : c.a0 ≠ Drift.pred P c.b0 := by
    intro he
    have hw0 := outs.1
    rw [he,← d0] at hw0
    contradiction
  have n1 : c.a1 ≠ Drift.pred P c.b1 := by
    intro he
    have hw1 := outs.2.2.1
    rw [he,← d1] at hw1
    contradiction
  have t0 : Drift.stableTime (2,-2) P w c.a0 ≠ Drift.stableTime (2,-2) P w (Drift.pred P c.b0) :=
    fun he => n0 (Drift.stableTime_injective c.a0_lt he0 he)
  have t1 : Drift.stableTime (2,-2) P w c.a1 ≠ Drift.stableTime (2,-2) P w (Drift.pred P c.b1) :=
    fun he => n1 (Drift.stableTime_injective c.a1_lt he1 he)
  exact ⟨h0.2.2.symm,h1.2.2.symm,d0.symm,d1.symm,by omega,by omega⟩

theorem core_total_gap {P : Nat} {w : Nat → Bool} (hw : ConsistentWord P w)
    (hd : wordDrift P w=(2,-2)) (c : Core P w) :
    (P : Int) = 4 +
      (Drift.stableTime (2,-2) P w (Drift.pred P c.b0)-Drift.stableTime (2,-2) P w c.a0) +
      (Drift.stableTime (2,-2) P w (Drift.pred P c.b1)-Drift.stableTime (2,-2) P w c.a1) := by
  have hv : ((2 : Int),(-2 : Int)) ≠ (0,0) := by decide
  have e := core_exit_data hw hd c
  have b := core_bridges hw hd c
  have o := core_outgoing hw c
  have t0 := Drift.successor_stableTime hd hv (UnitDiagonalMatching.pred_lt c.b0_lt)
  have t1 := Drift.successor_stableTime hd hv c.b0_lt
  have t2 := Drift.successor_stableTime hd hv (UnitDiagonalMatching.pred_lt c.b1_lt)
  have t3 := Drift.successor_stableTime hd hv c.b1_lt
  have s0 : Drift.succ P (Drift.pred P c.b0)=c.b0 := UnitDiagonalMatching.succ_pred c.b0_lt
  have s1 : Drift.succ P (Drift.pred P c.b1)=c.b1 := UnitDiagonalMatching.succ_pred c.b1_lt
  rw [s0,e.2.2.1,Drift.liftStep_congr e.1] at t0
  rw [b.1,o.2.2.2,liftStep_south] at t1
  rw [s1,e.2.2.2.1,Drift.liftStep_congr e.2.1] at t2
  rw [b.2,o.2.1,liftStep_south] at t3
  have c0 := firstPred_class_edge hw hd hv c.b0_lt
  have c1 := firstPred_class_edge hw hd hv c.a1_lt
  have c2 := firstPred_class_edge hw hd hv c.b1_lt
  have c3 := firstPred_class_edge hw hd hv c.a0_lt
  rw [c.edge3,c.dir3] at c0
  rw [c.edge2,c.dir2] at c1
  rw [c.edge1,c.dir1] at c2
  rw [c.edge0,c.dir0] at c3
  have v0 := liftStep_residue c0
  have v1 := liftStep_residue c1
  have v2 := liftStep_residue c2
  have v3 := liftStep_residue c3
  simp only [dx,move,liftStep_south] at v0 v1 v2 v3
  have vs : Drift.liftStep (2,-2) (wordPos w c.a0) .east +
      Drift.liftStep (2,-2) (wordPos w c.a1) .east=1 := by omega
  have vm := congrArg (fun x : Int => (P : Int)*x) vs
  simp only [Int.mul_add,Int.mul_one] at vm
  simp only [Int.mul_zero,Int.sub_zero] at t1 t3
  simp only [Drift.pred]
  omega


theorem exists_two_gate_decomposition {P : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hP : 0<P) (hd : wordDrift P w=(2,-2)) :
    ∃ c : Core P w, ∃ d0 d1 : Nat,
      0<d0 ∧ 0<d1 ∧ d0<P ∧ d1<P ∧ P=d0+d1+4 ∧
      Drift.succ P c.b0=c.a1 ∧ Drift.succ P c.b1=c.a0 ∧
      let p0 := ContinuousPhasePath.ofStart hP c.a0 d0
      let p1 := ContinuousPhasePath.ofStart hP c.a1 d1
      p0.phase d0=Drift.pred P c.b0 ∧ p0.pos w d0=p0.pos w 0 ∧
      p1.phase d1=Drift.pred P c.b1 ∧ p1.pos w d1=p1.pos w 0 := by
  have hv : ((2 : Int),(-2 : Int)) ≠ (0,0) := by decide
  obtain ⟨c⟩ := exists_core hw hP hd
  have e := core_exit_data hw hd c
  have b := core_bridges hw hd c
  have total := core_total_gap hw hd c
  let D0 := Drift.stableTime (2,-2) P w (Drift.pred P c.b0)-Drift.stableTime (2,-2) P w c.a0
  let D1 := Drift.stableTime (2,-2) P w (Drift.pred P c.b1)-Drift.stableTime (2,-2) P w c.a1
  have hd0 : 0<D0 := by dsimp [D0]; exact Int.sub_pos.mpr e.2.2.2.2.1
  have hd1 : 0<D1 := by dsimp [D1]; exact Int.sub_pos.mpr e.2.2.2.2.2
  have htotal : (P : Int)=4+D0+D1 := total
  have n0 : (D0.toNat : Int)=D0 := Int.toNat_of_nonneg (by omega)
  have n1 : (D1.toNat : Int)=D1 := Int.toNat_of_nonneg (by omega)
  have path0 := stable_gap_is_actual_closed_path hd hv c.a0_lt
    (UnitDiagonalMatching.pred_lt c.b0_lt) e.1 (len := D0.toNat)
    (by rw [n0]; dsimp [D0]; simp only [Drift.pred]; omega)
  have path1 := stable_gap_is_actual_closed_path hd hv c.a1_lt
    (UnitDiagonalMatching.pred_lt c.b1_lt) e.2.1 (len := D1.toNat)
    (by rw [n1]; dsimp [D1]; simp only [Drift.pred]; omega)
  exact ⟨c,D0.toNat,D1.toNat,by omega,by omega,by omega,by omega,by omega,
    b.1,b.2,path0.2.1,path0.2.2,path1.2.1,path1.2.2⟩


end LangtonsAnt.PersistA.TwoGateDecomposition
