import DiagonalMultipleLanes

namespace LangtonsAnt.PersistA.FirstVisitMap

open DiagonalMultipleLanes

def firstOf (v : Point) (P : Nat) (w : Nat → Bool) (i : Nat) : Nat :=
  classPhaseAtRank v P w (wordPos w i) 0

theorem firstOf_spec {v : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    firstOf v P w i ∈ Drift.classPhases v P w (wordPos w i) ∧
    Drift.stableRank P w (firstOf v P w i) = 0 := by
  have hm : i ∈ Drift.classPhases v P w (wordPos w i) :=
    Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩
  have hl := Drift.stableRank_lt_class_length hd hv hm
  exact classPhaseAtRank_spec hd hv (by omega)

theorem firstOf_time_le {v : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    Drift.stableTime v P w (firstOf v P w i) ≤ Drift.stableTime v P w i := by
  have hs := firstOf_spec hd hv hi
  obtain ⟨hfirst, hc⟩ := Drift.mem_classPhases.mp hs.1
  by_cases h : Drift.stableTime v P w i < Drift.stableTime v P w (firstOf v P w i)
  · have hr := Drift.stableRank_lt_of_stableTime_lt hd hv hi hfirst hc.symm h
    omega
  · omega

def firstPred (v : Point) (P : Nat) (w : Nat → Bool) (i : Nat) : Nat :=
  firstOf v P w (Drift.pred P i)

theorem firstPred_spec {v : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    firstPred v P w i < P ∧ Drift.stableRank P w (firstPred v P w i) = 0 ∧
    Drift.SameClass v (wordPos w (firstPred v P w i)) (wordPos w (Drift.pred P i)) := by
  have hs := firstOf_spec hd hv (UnitDiagonalMatching.pred_lt hi)
  obtain ⟨hp,hc⟩ := Drift.mem_classPhases.mp hs.1
  exact ⟨hp,hs.2,hc⟩

theorem firstPred_white {v : Point} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    w (firstPred v P w i) = false := by
  have hs := firstPred_spec hd hv hi
  rw [Drift.consistentWord_stableRank_color hw hs.1, hs.2.1]
  rfl

theorem firstPred_class_edge {v : Point} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    Drift.SameClass v
      (move (wordPos w (firstPred v P w i)) (Drift.inDir w i)) (wordPos w i) := by
  have hpi := UnitDiagonalMatching.pred_lt hi
  have hs := firstPred_spec hd hv hi
  have he := Drift.successor_class hd hpi
  have hdirection := Drift.successor_heading hw.1 hpi
  have hsp : Drift.succ P (UnitDiagonalMatching.pred P i) = i := UnitDiagonalMatching.succ_pred hi
  rw [hsp] at he hdirection
  rw [← hdirection] at he
  exact ((Drift.sameClass_move_iff v _ _ _).mpr hs.2.2).trans he.symm

theorem firstPred_clock {v : Point} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    Drift.stableTime v P w (firstPred v P w i) + 1 -
      (P : Int) * Drift.liftStep v (wordPos w (firstPred v P w i)) (Drift.inDir w i) ≤
      Drift.stableTime v P w i := by
  have hpi := UnitDiagonalMatching.pred_lt hi
  have hs := firstPred_spec hd hv hi
  have hle := firstOf_time_le hd hv hpi
  change Drift.stableTime v P w (firstPred v P w i) ≤
    Drift.stableTime v P w (Drift.pred P i) at hle
  have hclock := Drift.successor_stableTime hd hv hpi
  have hdirection := Drift.successor_heading hw.1 hpi
  have hsp : Drift.succ P (UnitDiagonalMatching.pred P i) = i := UnitDiagonalMatching.succ_pred hi
  rw [hsp] at hclock hdirection
  rw [← hdirection, ← Drift.liftStep_congr hs.2.2] at hclock
  simp only [Drift.pred] at hle
  omega


theorem rank_zero_time_le {v : Point} {P a b : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0,0)) (ha : a<P) (hb : b<P)
    (hr : Drift.stableRank P w a=0)
    (hc : Drift.SameClass v (wordPos w a) (wordPos w b)) :
    Drift.stableTime v P w a ≤ Drift.stableTime v P w b := by
  by_cases h : Drift.stableTime v P w b < Drift.stableTime v P w a
  · have := Drift.stableRank_lt_of_stableTime_lt hd hv hb ha hc.symm h
    omega
  · omega

theorem zero_port_successor {v : Point} {P a b : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0,0))
    (ha : a<P) (hb : b<P) (hrb : Drift.stableRank P w b=0)
    (hf : firstPred v P w b=a) (hout : Drift.outDir w a=Drift.inDir w b) :
    Drift.succ P a=b := by
  have hs := firstPred_spec hd hv hb
  have hc : Drift.SameClass v (wordPos w a) (wordPos w (Drift.pred P b)) := by
    simpa only [hf] using hs.2.2
  have hpi : Drift.pred P b<P := UnitDiagonalMatching.pred_lt hb
  have hsi : Drift.succ P a<P := UnitDiagonalMatching.succ_lt (by omega)
  have hclocka := Drift.successor_stableTime hd hv ha
  have hclockb := Drift.successor_stableTime hd hv hpi
  have hdir := Drift.successor_heading hw.1 hpi
  have hsp : Drift.succ P (Drift.pred P b)=b := UnitDiagonalMatching.succ_pred hb
  rw [hsp] at hclockb hdir
  rw [hout,Drift.liftStep_congr hc] at hclocka
  rw [← hdir] at hclockb
  have hle := firstOf_time_le hd hv hpi
  change Drift.stableTime v P w (firstPred v P w b) ≤ Drift.stableTime v P w (Drift.pred P b) at hle
  rw [hf] at hle
  have hab : Drift.SameClass v (wordPos w (Drift.succ P a)) (wordPos w b) := by
    have htarget := firstPred_class_edge hw hd hv hb
    rw [hf] at htarget
    have hnext := Drift.successor_class hd ha
    rw [hout] at hnext
    exact hnext.trans htarget
  have hreverse := rank_zero_time_le hd hv hb hsi hrb hab.symm
  apply Drift.stableTime_injective (v := v) (w := w) hsi hb
  omega


end LangtonsAnt.PersistA.FirstVisitMap
