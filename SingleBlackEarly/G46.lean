import FastCell2
import SegmentCheck
import SingleBlackEarly.C1702
import SingleBlackEarly.C1703
import SingleBlackEarly.C1704
import SingleBlackEarly.C1705
import SingleBlackEarly.C1706
import SingleBlackEarly.C1707
import SingleBlackEarly.C1708
import SingleBlackEarly.C1709
import SingleBlackEarly.C1710
import SingleBlackEarly.C1711
import SingleBlackEarly.C1712
import SingleBlackEarly.C1713
import SingleBlackEarly.C1714
import SingleBlackEarly.C1715
import SingleBlackEarly.C1716
import SingleBlackEarly.C1717
import SingleBlackEarly.C1718
import SingleBlackEarly.C1719
import SingleBlackEarly.C1720
import SingleBlackEarly.C1721
import SingleBlackEarly.C1722
import SingleBlackEarly.C1723
import SingleBlackEarly.C1724
import SingleBlackEarly.C1725
import SingleBlackEarly.C1726
import SingleBlackEarly.C1727
import SingleBlackEarly.C1728
import SingleBlackEarly.C1729
import SingleBlackEarly.C1730
import SingleBlackEarly.C1731
import SingleBlackEarly.C1732
import SingleBlackEarly.C1733
import SingleBlackEarly.C1734
import SingleBlackEarly.C1735
import SingleBlackEarly.C1736
import SingleBlackEarly.C1737
import SingleBlackEarly.C1738

namespace LangtonsAnt

def sbGroup46 : List Point :=
  [(-44, -26), (-45, -26), (-44, -24), (-43, -25), (-47, -21), (-48, -21), (-48, -20), (-48, -22), (-49, -22), (-49, -21), (-47, -22), (-48, -23), (-47, -25), (-48, -25), (-48, -24), (-48, -26), (-49, -26), (-49, -25), (-47, -26), (-47, -27), (-48, -27), (-46, -27), (-46, -28), (-47, -28), (-46, -26), (-45, -27), (-49, -23), (-50, -23), (-50, -22), (-50, -24), (-51, -24), (-51, -23), (-49, -24), (-50, -25), (-49, -27), (-50, -27), (-50, -26)]

theorem sbGroup46_ok : forall q, q ∈ sbGroup46 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup46, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1702
  · exact sbCell1703
  · exact checkSingleBlackFast2_sound sbCell1704
  · exact checkSingleBlackFast_sound sbCell1705
  · exact checkSingleBlackFast2_sound sbCell1706
  · exact checkSingleBlackFast_sound sbCell1707
  · exact checkSingleBlackFast2_sound sbCell1708
  · exact checkSingleBlackFast_sound sbCell1709
  · exact checkSingleBlackFast2_sound sbCell1710
  · exact checkSingleBlackFast_sound sbCell1711
  · exact checkSingleBlackFast_sound sbCell1712
  · exact checkSingleBlackFast2_sound sbCell1713
  · exact checkSingleBlackFast2_sound sbCell1714
  · exact checkSingleBlackFast_sound sbCell1715
  · exact checkSingleBlack_sound sbCell1716
  · exact checkSingleBlackFast2_sound sbCell1717
  · exact checkSingleBlackFast2_sound sbCell1718
  · exact checkSingleBlackFast_sound sbCell1719
  · exact checkSingleBlack_sound sbCell1720
  · exact checkSingleBlack_sound sbCell1721
  · exact checkSingleBlackFast2_sound sbCell1722
  · exact checkSingleBlackFast_sound sbCell1723
  · exact checkSingleBlackFast_sound sbCell1724
  · exact sbCell1725
  · exact checkSingleBlackFast2_sound sbCell1726
  · exact checkSingleBlackFast_sound sbCell1727
  · exact checkSingleBlackFast2_sound sbCell1728
  · exact checkSingleBlackFast_sound sbCell1729
  · exact checkSingleBlack_sound sbCell1730
  · exact checkSingleBlackFast_sound sbCell1731
  · exact checkSingleBlack_sound sbCell1732
  · exact checkSingleBlackFast_sound sbCell1733
  · exact checkSingleBlackFast_sound sbCell1734
  · exact checkSingleBlackFast2_sound sbCell1735
  · exact checkSingleBlackFast2_sound sbCell1736
  · exact checkSingleBlackFast_sound sbCell1737
  · exact checkSingleBlack_sound sbCell1738

end LangtonsAnt
