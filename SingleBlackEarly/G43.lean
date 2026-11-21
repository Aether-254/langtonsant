import FastCell2
import SegmentCheck
import SingleBlackEarly.C1591
import SingleBlackEarly.C1592
import SingleBlackEarly.C1593
import SingleBlackEarly.C1594
import SingleBlackEarly.C1595
import SingleBlackEarly.C1596
import SingleBlackEarly.C1597
import SingleBlackEarly.C1598
import SingleBlackEarly.C1599
import SingleBlackEarly.C1600
import SingleBlackEarly.C1601
import SingleBlackEarly.C1602
import SingleBlackEarly.C1603
import SingleBlackEarly.C1604
import SingleBlackEarly.C1605
import SingleBlackEarly.C1606
import SingleBlackEarly.C1607
import SingleBlackEarly.C1608
import SingleBlackEarly.C1609
import SingleBlackEarly.C1610
import SingleBlackEarly.C1611
import SingleBlackEarly.C1612
import SingleBlackEarly.C1613
import SingleBlackEarly.C1614
import SingleBlackEarly.C1615
import SingleBlackEarly.C1616
import SingleBlackEarly.C1617
import SingleBlackEarly.C1618
import SingleBlackEarly.C1619
import SingleBlackEarly.C1620
import SingleBlackEarly.C1621
import SingleBlackEarly.C1622
import SingleBlackEarly.C1623
import SingleBlackEarly.C1624
import SingleBlackEarly.C1625
import SingleBlackEarly.C1626
import SingleBlackEarly.C1627

namespace LangtonsAnt

def sbGroup43 : List Point :=
  [(-34, -15), (-34, -16), (-35, -16), (-34, -14), (-33, -15), (-37, -11), (-38, -11), (-38, -10), (-38, -12), (-39, -12), (-39, -11), (-37, -12), (-38, -13), (-37, -15), (-38, -15), (-38, -14), (-38, -16), (-39, -16), (-39, -15), (-37, -16), (-37, -17), (-38, -17), (-36, -17), (-36, -18), (-37, -18), (-36, -16), (-35, -17), (-39, -13), (-40, -13), (-40, -12), (-40, -14), (-41, -14), (-41, -13), (-39, -14), (-40, -15), (-39, -17), (-40, -17)]

theorem sbGroup43_ok : forall q, q ∈ sbGroup43 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup43, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1591
  · exact checkSingleBlackFast_sound sbCell1592
  · exact checkSingleBlackFast_sound sbCell1593
  · exact checkSingleBlack_sound sbCell1594
  · exact checkSingleBlackFast_sound sbCell1595
  · exact checkSingleBlackFast2_sound sbCell1596
  · exact checkSingleBlackFast_sound sbCell1597
  · exact checkSingleBlackFast2_sound sbCell1598
  · exact checkSingleBlackFast_sound sbCell1599
  · exact checkSingleBlackFast_sound sbCell1600
  · exact checkSingleBlackFast_sound sbCell1601
  · exact checkSingleBlackFast_sound sbCell1602
  · exact checkSingleBlackFast_sound sbCell1603
  · exact checkSingleBlack_sound sbCell1604
  · exact checkSingleBlackFast_sound sbCell1605
  · exact checkSingleBlack_sound sbCell1606
  · exact checkSingleBlackFast_sound sbCell1607
  · exact checkSingleBlackFast2_sound sbCell1608
  · exact checkSingleBlackFast_sound sbCell1609
  · exact checkSingleBlack_sound sbCell1610
  · exact checkSingleBlackFast_sound sbCell1611
  · exact checkSingleBlackFast_sound sbCell1612
  · exact checkSingleBlackFast_sound sbCell1613
  · exact checkSingleBlackFast_sound sbCell1614
  · exact sbCell1615
  · exact checkSingleBlack_sound sbCell1616
  · exact checkSingleBlackFast_sound sbCell1617
  · exact checkSingleBlackFast2_sound sbCell1618
  · exact checkSingleBlackFast_sound sbCell1619
  · exact checkSingleBlackFast2_sound sbCell1620
  · exact checkSingleBlackFast_sound sbCell1621
  · exact checkSingleBlackFast_sound sbCell1622
  · exact checkSingleBlackFast_sound sbCell1623
  · exact checkSingleBlackFast_sound sbCell1624
  · exact checkSingleBlackFast2_sound sbCell1625
  · exact checkSingleBlack_sound sbCell1626
  · exact checkSingleBlackFast_sound sbCell1627

end LangtonsAnt
