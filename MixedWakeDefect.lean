import TwoCellDiagonalExtremal

/-!
# Mixed-wake defect identity for full drift `(2,-2)`

For a periodic word with full drift `(2,-2)` and final heading north, the exact two-lane flow laws
of `TwoCellDiagonalExtremal` combine into a mod-2 identity linking the horizontal departures of
two consecutive even layers with the visit multiplicities of those layers.  When every even layer
has even multiplicity (`PureOddWake`), the right-hand side vanishes; the standard 104-step
highway has `classMult = 3` on layer `0`, so it is a *mixed* wake and the homogeneous
specialisation does not apply to it.

Pure kernel proofs (`decide +kernel` for the concrete standard-word facts); no `native_decide`.
Origin: brainstorm round 2, topic T3 (`research/brainstorm2-T3-width-2026-11-22.md`, §2 and §7).
-/

namespace LangtonsAnt.MixedWakeDefect
open TwoCellDiagonal

/-- **Mod-2 defect identity.**  Around an even layer pair `t, t+2` the horizontal departures and
the northward departures of the adjacent odd layers have the parity of the two class
multiplicities. -/
theorem mixed_step_defect {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, -2))
    {t : Int} (ht : t % 2 = 0) (r : Bool) :
    (eCnt P w (t + 2) r + nCnt P w (t + 1) (!r) +
      eCnt P w t r + nCnt P w (t - 1) (!r)) % 2 =
    (classMult P w t (!r) + classMult P w (t + 2) r) % 2 := by
  have hf := odd_layer_flow_eq hh hd (show (t + 1) % 2 = 1 by omega) (!r)
  have ha := even_layer_arr_sum hh hd ht (!r)
  have he := even_layer_dep_sum (P := P) (w := w) (show (t + 2) % 2 = 0 by omega) r
  rw [Bool.not_not] at hf
  have ht2 : t + 1 + 1 = t + 2 := by omega
  have ht0 : t + 1 - 1 = t := by omega
  rw [ht2, ht0] at hf
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Concrete defect data of the standard highway at layers `0` and `-2`. -/
theorem stdHighwaySE_defect :
    classMult 104 stdHighwaySE 0 false = 3 ∧
    eCnt 104 stdHighwaySE 0 false = 2 ∧
    nCnt 104 stdHighwaySE (-1) true = 1 ∧
    classMult 104 stdHighwaySE (-2) true = 0 ∧
    eCnt 104 stdHighwaySE (-2) false = 0 ∧
    nCnt 104 stdHighwaySE (-3) true = 0 := by
  decide +kernel

/-- The standard highway is not a pure-odd wake: the homogeneous case of the defect identity
does not cover it. -/
theorem stdHighwaySE_not_pureOddWake : ¬ PureOddWake 104 stdHighwaySE := by
  intro hp
  have hm := (pureOddWake_iff_even_classMult_even stdHighwaySE_drift).mp hp
    0 false (by decide)
  rw [stdHighwaySE_defect.1] at hm
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Interface counts of the standard highway: in each lane exactly one west departure from
layer `0`, one north departure from layer `-1`, one east departure from layer `8` and one south
departure from layer `9`. -/
theorem stdHighwaySE_interfaces :
    ∀ r : Bool,
      wCnt 104 stdHighwaySE 0 r = 1 ∧
      nCnt 104 stdHighwaySE (-1) r = 1 ∧
      eCnt 104 stdHighwaySE 8 r = 1 ∧
      sCnt 104 stdHighwaySE 9 r = 1 := by
  decide +kernel

end LangtonsAnt.MixedWakeDefect
