import FastCell2
import SegmentCheck
import SingleBlackEarly.C1665
import SingleBlackEarly.C1666
import SingleBlackEarly.C1667
import SingleBlackEarly.C1668
import SingleBlackEarly.C1669
import SingleBlackEarly.C1670
import SingleBlackEarly.C1671
import SingleBlackEarly.C1672
import SingleBlackEarly.C1673
import SingleBlackEarly.C1674
import SingleBlackEarly.C1675
import SingleBlackEarly.C1676
import SingleBlackEarly.C1677
import SingleBlackEarly.C1678
import SingleBlackEarly.C1679
import SingleBlackEarly.C1680
import SingleBlackEarly.C1681
import SingleBlackEarly.C1682
import SingleBlackEarly.C1683
import SingleBlackEarly.C1684
import SingleBlackEarly.C1685
import SingleBlackEarly.C1686
import SingleBlackEarly.C1687
import SingleBlackEarly.C1688
import SingleBlackEarly.C1689
import SingleBlackEarly.C1690
import SingleBlackEarly.C1691
import SingleBlackEarly.C1692
import SingleBlackEarly.C1693
import SingleBlackEarly.C1694
import SingleBlackEarly.C1695
import SingleBlackEarly.C1696
import SingleBlackEarly.C1697
import SingleBlackEarly.C1698
import SingleBlackEarly.C1699
import SingleBlackEarly.C1700
import SingleBlackEarly.C1701

namespace LangtonsAnt

def sbGroup45 : List Point :=
  [(-44, -18), (-45, -18), (-45, -17), (-43, -18), (-44, -19), (-43, -21), (-44, -21), (-44, -20), (-44, -22), (-45, -22), (-45, -21), (-43, -22), (-43, -23), (-44, -23), (-42, -23), (-42, -24), (-43, -24), (-42, -22), (-41, -23), (-45, -19), (-46, -19), (-46, -18), (-46, -20), (-47, -20), (-47, -19), (-45, -20), (-46, -21), (-45, -23), (-46, -23), (-46, -22), (-46, -24), (-47, -24), (-47, -23), (-45, -24), (-45, -25), (-46, -25), (-44, -25)]

theorem sbGroup45_ok : forall q, q ∈ sbGroup45 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup45, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1665
  · exact checkSingleBlackFast_sound sbCell1666
  · exact checkSingleBlackFast_sound sbCell1667
  · exact checkSingleBlackFast_sound sbCell1668
  · exact checkSingleBlackFast2_sound sbCell1669
  · exact checkSingleBlack_sound sbCell1670
  · exact checkSingleBlackFast_sound sbCell1671
  · exact checkSingleBlack_sound sbCell1672
  · exact checkSingleBlackFast_sound sbCell1673
  · exact checkSingleBlackFast2_sound sbCell1674
  · exact checkSingleBlackFast_sound sbCell1675
  · exact checkSingleBlack_sound sbCell1676
  · exact checkSingleBlack_sound sbCell1677
  · exact checkSingleBlackFast_sound sbCell1678
  · exact checkSingleBlackFast_sound sbCell1679
  · exact checkSingleBlackFast_sound sbCell1680
  · exact sbCell1681
  · exact checkSingleBlackFast2_sound sbCell1682
  · exact checkSingleBlackFast_sound sbCell1683
  · exact checkSingleBlackFast2_sound sbCell1684
  · exact checkSingleBlackFast_sound sbCell1685
  · exact checkSingleBlackFast2_sound sbCell1686
  · exact checkSingleBlackFast_sound sbCell1687
  · exact checkSingleBlackFast_sound sbCell1688
  · exact checkSingleBlackFast2_sound sbCell1689
  · exact checkSingleBlackFast_sound sbCell1690
  · exact checkSingleBlackFast2_sound sbCell1691
  · exact checkSingleBlackFast2_sound sbCell1692
  · exact checkSingleBlackFast2_sound sbCell1693
  · exact checkSingleBlack_sound sbCell1694
  · exact checkSingleBlackFast_sound sbCell1695
  · exact checkSingleBlackFast2_sound sbCell1696
  · exact checkSingleBlackFast_sound sbCell1697
  · exact checkSingleBlack_sound sbCell1698
  · exact sbCell1699
  · exact checkSingleBlack_sound sbCell1700
  · exact checkSingleBlackFast_sound sbCell1701

end LangtonsAnt
