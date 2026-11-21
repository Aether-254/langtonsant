import FastCell2
import SegmentCheck
import SingleBlackEarly.C1628
import SingleBlackEarly.C1629
import SingleBlackEarly.C1630
import SingleBlackEarly.C1631
import SingleBlackEarly.C1632
import SingleBlackEarly.C1633
import SingleBlackEarly.C1634
import SingleBlackEarly.C1635
import SingleBlackEarly.C1636
import SingleBlackEarly.C1637
import SingleBlackEarly.C1638
import SingleBlackEarly.C1639
import SingleBlackEarly.C1640
import SingleBlackEarly.C1641
import SingleBlackEarly.C1642
import SingleBlackEarly.C1643
import SingleBlackEarly.C1644
import SingleBlackEarly.C1645
import SingleBlackEarly.C1646
import SingleBlackEarly.C1647
import SingleBlackEarly.C1648
import SingleBlackEarly.C1649
import SingleBlackEarly.C1650
import SingleBlackEarly.C1651
import SingleBlackEarly.C1652
import SingleBlackEarly.C1653
import SingleBlackEarly.C1654
import SingleBlackEarly.C1655
import SingleBlackEarly.C1656
import SingleBlackEarly.C1657
import SingleBlackEarly.C1658
import SingleBlackEarly.C1659
import SingleBlackEarly.C1660
import SingleBlackEarly.C1661
import SingleBlackEarly.C1662
import SingleBlackEarly.C1663
import SingleBlackEarly.C1664

namespace LangtonsAnt

def sbGroup44 : List Point :=
  [(-40, -16), (-40, -18), (-41, -18), (-41, -17), (-39, -18), (-39, -19), (-40, -19), (-38, -19), (-38, -20), (-39, -20), (-38, -18), (-37, -19), (-41, -15), (-42, -15), (-42, -14), (-42, -16), (-43, -16), (-43, -15), (-41, -16), (-42, -17), (-41, -19), (-42, -19), (-42, -18), (-42, -20), (-43, -20), (-43, -19), (-41, -20), (-41, -21), (-42, -21), (-40, -21), (-40, -22), (-41, -22), (-40, -20), (-39, -21), (-43, -17), (-44, -17), (-44, -16)]

theorem sbGroup44_ok : forall q, q ∈ sbGroup44 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup44, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlack_sound sbCell1628
  · exact checkSingleBlackFast2_sound sbCell1629
  · exact checkSingleBlackFast2_sound sbCell1630
  · exact checkSingleBlackFast_sound sbCell1631
  · exact checkSingleBlack_sound sbCell1632
  · exact sbCell1633
  · exact checkSingleBlackFast_sound sbCell1634
  · exact checkSingleBlackFast_sound sbCell1635
  · exact checkSingleBlackFast_sound sbCell1636
  · exact sbCell1637
  · exact checkSingleBlack_sound sbCell1638
  · exact checkSingleBlackFast_sound sbCell1639
  · exact checkSingleBlackFast2_sound sbCell1640
  · exact checkSingleBlackFast_sound sbCell1641
  · exact checkSingleBlackFast2_sound sbCell1642
  · exact checkSingleBlackFast_sound sbCell1643
  · exact checkSingleBlackFast_sound sbCell1644
  · exact sbCell1645
  · exact checkSingleBlackFast_sound sbCell1646
  · exact checkSingleBlackFast2_sound sbCell1647
  · exact checkSingleBlack_sound sbCell1648
  · exact checkSingleBlackFast_sound sbCell1649
  · exact checkSingleBlack_sound sbCell1650
  · exact sbCell1651
  · exact checkSingleBlackFast2_sound sbCell1652
  · exact checkSingleBlackFast_sound sbCell1653
  · exact checkSingleBlack_sound sbCell1654
  · exact sbCell1655
  · exact checkSingleBlackFast_sound sbCell1656
  · exact checkSingleBlackFast_sound sbCell1657
  · exact checkSingleBlackFast_sound sbCell1658
  · exact sbCell1659
  · exact checkSingleBlack_sound sbCell1660
  · exact checkSingleBlackFast_sound sbCell1661
  · exact checkSingleBlackFast2_sound sbCell1662
  · exact checkSingleBlackFast_sound sbCell1663
  · exact checkSingleBlackFast2_sound sbCell1664

end LangtonsAnt
