import FastCell2
import SegmentCheck
import SingleBlackEarly.C1739
import SingleBlackEarly.C1740
import SingleBlackEarly.C1741
import SingleBlackEarly.C1742
import SingleBlackEarly.C1743
import SingleBlackEarly.C1744
import SingleBlackEarly.C1745
import SingleBlackEarly.C1746
import SingleBlackEarly.C1747
import SingleBlackEarly.C1748
import SingleBlackEarly.C1749
import SingleBlackEarly.C1750
import SingleBlackEarly.C1751
import SingleBlackEarly.C1752
import SingleBlackEarly.C1753
import SingleBlackEarly.C1754
import SingleBlackEarly.C1755
import SingleBlackEarly.C1756
import SingleBlackEarly.C1757
import SingleBlackEarly.C1758
import SingleBlackEarly.C1759
import SingleBlackEarly.C1760
import SingleBlackEarly.C1761
import SingleBlackEarly.C1762
import SingleBlackEarly.C1763
import SingleBlackEarly.C1764
import SingleBlackEarly.C1765
import SingleBlackEarly.C1766
import SingleBlackEarly.C1767
import SingleBlackEarly.C1768
import SingleBlackEarly.C1769
import SingleBlackEarly.C1770
import SingleBlackEarly.C1771
import SingleBlackEarly.C1772
import SingleBlackEarly.C1773
import SingleBlackEarly.C1774
import SingleBlackEarly.C1775

namespace LangtonsAnt

def sbGroup47 : List Point :=
  [(-50, -28), (-51, -28), (-51, -27), (-49, -28), (-49, -29), (-50, -29), (-48, -29), (-48, -30), (-49, -30), (-48, -28), (-47, -29), (-51, -25), (-52, -25), (-52, -24), (-52, -26), (-53, -26), (-53, -25), (-51, -26), (-52, -27), (-51, -29), (-52, -29), (-52, -28), (-52, -30), (-53, -30), (-53, -29), (-51, -30), (-51, -31), (-52, -31), (-50, -31), (-50, -32), (-51, -32), (-50, -30), (-49, -31), (-53, -27), (-54, -27), (-54, -26), (-54, -28)]

theorem sbGroup47_ok : forall q, q ∈ sbGroup47 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup47, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1739
  · exact checkSingleBlackFast2_sound sbCell1740
  · exact checkSingleBlackFast_sound sbCell1741
  · exact checkSingleBlack_sound sbCell1742
  · exact checkSingleBlack_sound sbCell1743
  · exact checkSingleBlackFast2_sound sbCell1744
  · exact checkSingleBlackFast2_sound sbCell1745
  · exact checkSingleBlackFast_sound sbCell1746
  · exact sbCell1747
  · exact checkSingleBlackFast2_sound sbCell1748
  · exact checkSingleBlackFast_sound sbCell1749
  · exact checkSingleBlackFast2_sound sbCell1750
  · exact checkSingleBlackFast_sound sbCell1751
  · exact checkSingleBlackFast2_sound sbCell1752
  · exact checkSingleBlackFast_sound sbCell1753
  · exact checkSingleBlackFast2_sound sbCell1754
  · exact checkSingleBlackFast_sound sbCell1755
  · exact checkSingleBlackFast_sound sbCell1756
  · exact checkSingleBlackFast2_sound sbCell1757
  · exact checkSingleBlackFast2_sound sbCell1758
  · exact checkSingleBlackFast_sound sbCell1759
  · exact checkSingleBlack_sound sbCell1760
  · exact checkSingleBlackFast2_sound sbCell1761
  · exact checkSingleBlackFast_sound sbCell1762
  · exact checkSingleBlackFast_sound sbCell1763
  · exact checkSingleBlack_sound sbCell1764
  · exact checkSingleBlack_sound sbCell1765
  · exact checkSingleBlackFast_sound sbCell1766
  · exact checkSingleBlackFast_sound sbCell1767
  · exact checkSingleBlackFast2_sound sbCell1768
  · exact sbCell1769
  · exact checkSingleBlackFast2_sound sbCell1770
  · exact checkSingleBlackFast_sound sbCell1771
  · exact checkSingleBlackFast2_sound sbCell1772
  · exact checkSingleBlackFast_sound sbCell1773
  · exact checkSingleBlackFast2_sound sbCell1774
  · exact checkSingleBlackFast_sound sbCell1775

end LangtonsAnt
