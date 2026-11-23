import DriftRank

namespace LangtonsAnt.PersistA.TimingCircuit

def totalCost : List (Int × Int) → Int
  | [] => 0
  | e :: es => e.1 + totalCost es

def totalVoltage : List (Int × Int) → Int
  | [] => 0
  | e :: es => e.2 + totalVoltage es

inductive ClockWalk (P : Int) : Int → Int → List (Int × Int) → Prop where
  | nil (a : Int) : ClockWalk P a a []
  | cons {a b c : Int} {cost voltage : Int} {es : List (Int × Int)}
      (edge : a + cost - P * voltage ≤ b)
      (rest : ClockWalk P b c es) :
      ClockWalk P a c ((cost, voltage) :: es)

theorem walk_budget {P a b : Int} {es : List (Int × Int)}
    (h : ClockWalk P a b es) :
    a + totalCost es - P * totalVoltage es ≤ b := by
  induction h with
  | nil a => simp [totalCost, totalVoltage]
  | @cons a b c cost voltage es edge rest ih =>
      simp only [totalCost, totalVoltage, Int.mul_add]
      omega

theorem circuit_budget {P a : Int} {es : List (Int × Int)}
    (h : ClockWalk P a a es) :
    totalCost es ≤ P * totalVoltage es := by
  have hb := walk_budget h
  omega

theorem circuit_positive_voltage {P a : Int} {es : List (Int × Int)}
    (hP : 0 ≤ P) (h : ClockWalk P a a es)
    (hc : 0 < totalCost es) : 0 < totalVoltage es := by
  have hb := circuit_budget h
  apply Classical.byContradiction
  intro hn
  have hv : totalVoltage es ≤ 0 := by omega
  have hm := Int.mul_nonpos_of_nonneg_of_nonpos hP hv
  omega

theorem return_segment_voltage_positive {P len voltage ta tb : Int}
    (hP : 0 ≤ P) (hlen : 0 < len)
    (hsegment : ta - tb = len - P * voltage)
    (horder : ta < tb) : 0 < voltage := by
  apply Classical.byContradiction
  intro hn
  have hv : voltage ≤ 0 := by omega
  have hm := Int.mul_nonpos_of_nonneg_of_nonpos hP hv
  omega


theorem two_gate_budget {P a0 a1 e0 e1 : Int}
    (bridge0 : a1 - e0 = 2) (bridge1 : a0 - e1 = 2 - P)
    (order0 : a0 < e0) (order1 : a1 < e1) :
    P = 4 + (e0 - a0) + (e1 - a1) ∧
    0 < e0 - a0 ∧ e0 - a0 < P ∧
    0 < e1 - a1 ∧ e1 - a1 < P := by
  omega


end LangtonsAnt.PersistA.TimingCircuit
