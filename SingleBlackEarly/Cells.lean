import SingleBlackCheck
import SingleBlackEarly.G00
import SingleBlackEarly.G01
import SingleBlackEarly.G02
import SingleBlackEarly.G03
import SingleBlackEarly.G04
import SingleBlackEarly.G05
import SingleBlackEarly.G06
import SingleBlackEarly.G07
import SingleBlackEarly.G08
import SingleBlackEarly.G09
import SingleBlackEarly.G10
import SingleBlackEarly.G11
import SingleBlackEarly.G12
import SingleBlackEarly.G13
import SingleBlackEarly.G14
import SingleBlackEarly.G15
import SingleBlackEarly.G16
import SingleBlackEarly.G17
import SingleBlackEarly.G18
import SingleBlackEarly.G19
import SingleBlackEarly.G20
import SingleBlackEarly.G21
import SingleBlackEarly.G22
import SingleBlackEarly.G23
import SingleBlackEarly.G24
import SingleBlackEarly.G25
import SingleBlackEarly.G26
import SingleBlackEarly.G27
import SingleBlackEarly.G28
import SingleBlackEarly.G29
import SingleBlackEarly.G30
import SingleBlackEarly.G31
import SingleBlackEarly.G32
import SingleBlackEarly.G33
import SingleBlackEarly.G34
import SingleBlackEarly.G35
import SingleBlackEarly.G36
import SingleBlackEarly.G37
import SingleBlackEarly.G38
import SingleBlackEarly.G39
import SingleBlackEarly.G40
import SingleBlackEarly.G41
import SingleBlackEarly.G42
import SingleBlackEarly.G43
import SingleBlackEarly.G44
import SingleBlackEarly.G45
import SingleBlackEarly.G46
import SingleBlackEarly.G47
import SingleBlackEarly.G48
import SingleBlackEarly.G49
import SingleBlackEarly.G50
import SingleBlackEarly.G51
import SingleBlackEarly.G52
import SingleBlackEarly.G53
import SingleBlackEarly.G54
import SingleBlackEarly.G55
import SingleBlackEarly.G56
import SingleBlackEarly.G57
import SingleBlackEarly.G58
import SingleBlackEarly.G59

/-! Generated: the union of all early single-black cells and their certificates. -/

namespace LangtonsAnt

theorem ok_append {P : Point -> Prop} {a b : List Point}
    (ha : forall q, q ∈ a -> P q) (hb : forall q, q ∈ b -> P q) :
    forall q, q ∈ a ++ b -> P q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact ha q h
  · exact hb q h

def earlyCells : List Point :=
  sbGroup00 ++ sbGroup01 ++ sbGroup02 ++ sbGroup03 ++ sbGroup04 ++ sbGroup05 ++ sbGroup06 ++ sbGroup07 ++ sbGroup08 ++ sbGroup09 ++ sbGroup10 ++ sbGroup11 ++ sbGroup12 ++ sbGroup13 ++ sbGroup14 ++ sbGroup15 ++ sbGroup16 ++ sbGroup17 ++ sbGroup18 ++ sbGroup19 ++ sbGroup20 ++ sbGroup21 ++ sbGroup22 ++ sbGroup23 ++ sbGroup24 ++ sbGroup25 ++ sbGroup26 ++ sbGroup27 ++ sbGroup28 ++ sbGroup29 ++ sbGroup30 ++ sbGroup31 ++ sbGroup32 ++ sbGroup33 ++ sbGroup34 ++ sbGroup35 ++ sbGroup36 ++ sbGroup37 ++ sbGroup38 ++ sbGroup39 ++ sbGroup40 ++ sbGroup41 ++ sbGroup42 ++ sbGroup43 ++ sbGroup44 ++ sbGroup45 ++ sbGroup46 ++ sbGroup47 ++ sbGroup48 ++ sbGroup49 ++ sbGroup50 ++ sbGroup51 ++ sbGroup52 ++ sbGroup53 ++ sbGroup54 ++ sbGroup55 ++ sbGroup56 ++ sbGroup57 ++ sbGroup58 ++ sbGroup59

theorem earlyCells_ok : forall q, q ∈ earlyCells -> EventuallyStandard (singleBlack q) := by
  unfold earlyCells
  exact (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append (ok_append sbGroup00_ok sbGroup01_ok) sbGroup02_ok) sbGroup03_ok) sbGroup04_ok) sbGroup05_ok) sbGroup06_ok) sbGroup07_ok) sbGroup08_ok) sbGroup09_ok) sbGroup10_ok) sbGroup11_ok) sbGroup12_ok) sbGroup13_ok) sbGroup14_ok) sbGroup15_ok) sbGroup16_ok) sbGroup17_ok) sbGroup18_ok) sbGroup19_ok) sbGroup20_ok) sbGroup21_ok) sbGroup22_ok) sbGroup23_ok) sbGroup24_ok) sbGroup25_ok) sbGroup26_ok) sbGroup27_ok) sbGroup28_ok) sbGroup29_ok) sbGroup30_ok) sbGroup31_ok) sbGroup32_ok) sbGroup33_ok) sbGroup34_ok) sbGroup35_ok) sbGroup36_ok) sbGroup37_ok) sbGroup38_ok) sbGroup39_ok) sbGroup40_ok) sbGroup41_ok) sbGroup42_ok) sbGroup43_ok) sbGroup44_ok) sbGroup45_ok) sbGroup46_ok) sbGroup47_ok) sbGroup48_ok) sbGroup49_ok) sbGroup50_ok) sbGroup51_ok) sbGroup52_ok) sbGroup53_ok) sbGroup54_ok) sbGroup55_ok) sbGroup56_ok) sbGroup57_ok) sbGroup58_ok) sbGroup59_ok)

end LangtonsAnt
