import FastCell2
import SegmentCheck
import SingleBlackEarly.C1776
import SingleBlackEarly.C1777
import SingleBlackEarly.C1778
import SingleBlackEarly.C1779
import SingleBlackEarly.C1780
import SingleBlackEarly.C1781
import SingleBlackEarly.C1782
import SingleBlackEarly.C1783
import SingleBlackEarly.C1784
import SingleBlackEarly.C1785
import SingleBlackEarly.C1786
import SingleBlackEarly.C1787
import SingleBlackEarly.C1788
import SingleBlackEarly.C1789
import SingleBlackEarly.C1790
import SingleBlackEarly.C1791
import SingleBlackEarly.C1792
import SingleBlackEarly.C1793
import SingleBlackEarly.C1794
import SingleBlackEarly.C1795
import SingleBlackEarly.C1796
import SingleBlackEarly.C1797
import SingleBlackEarly.C1798
import SingleBlackEarly.C1799
import SingleBlackEarly.C1800
import SingleBlackEarly.C1801
import SingleBlackEarly.C1802
import SingleBlackEarly.C1803
import SingleBlackEarly.C1804
import SingleBlackEarly.C1805
import SingleBlackEarly.C1806
import SingleBlackEarly.C1807
import SingleBlackEarly.C1808
import SingleBlackEarly.C1809
import SingleBlackEarly.C1810
import SingleBlackEarly.C1811
import SingleBlackEarly.C1812

namespace LangtonsAnt

def sbGroup48 : List Point :=
  [(-55, -28), (-55, -27), (-53, -28), (-54, -29), (-53, -31), (-54, -31), (-54, -30), (-54, -32), (-55, -32), (-55, -31), (-53, -32), (-53, -33), (-54, -33), (-52, -33), (-52, -34), (-53, -34), (-52, -32), (-51, -33), (-55, -29), (-56, -29), (-56, -28), (-56, -30), (-57, -30), (-57, -29), (-55, -30), (-56, -31), (-55, -33), (-56, -33), (-56, -32), (-56, -34), (-57, -34), (-57, -33), (-55, -34), (-55, -35), (-56, -35), (-54, -35), (-54, -36)]

theorem sbGroup48_ok : forall q, q ∈ sbGroup48 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup48, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1776
  · exact checkSingleBlackFast_sound sbCell1777
  · exact checkSingleBlackFast_sound sbCell1778
  · exact checkSingleBlackFast2_sound sbCell1779
  · exact checkSingleBlackFast2_sound sbCell1780
  · exact checkSingleBlackFast_sound sbCell1781
  · exact checkSingleBlack_sound sbCell1782
  · exact checkSingleBlackFast2_sound sbCell1783
  · exact checkSingleBlackFast_sound sbCell1784
  · exact checkSingleBlackFast_sound sbCell1785
  · exact checkSingleBlack_sound sbCell1786
  · exact checkSingleBlack_sound sbCell1787
  · exact checkSingleBlackFast_sound sbCell1788
  · exact checkSingleBlackFast_sound sbCell1789
  · exact checkSingleBlackFast_sound sbCell1790
  · exact sbCell1791
  · exact checkSingleBlackFast2_sound sbCell1792
  · exact checkSingleBlackFast_sound sbCell1793
  · exact checkSingleBlackFast2_sound sbCell1794
  · exact checkSingleBlackFast_sound sbCell1795
  · exact checkSingleBlackFast2_sound sbCell1796
  · exact checkSingleBlackFast_sound sbCell1797
  · exact checkSingleBlackFast2_sound sbCell1798
  · exact checkSingleBlackFast_sound sbCell1799
  · exact checkSingleBlackFast_sound sbCell1800
  · exact checkSingleBlackFast2_sound sbCell1801
  · exact checkSingleBlackFast2_sound sbCell1802
  · exact checkSingleBlackFast_sound sbCell1803
  · exact checkSingleBlack_sound sbCell1804
  · exact checkSingleBlackFast2_sound sbCell1805
  · exact checkSingleBlackFast_sound sbCell1806
  · exact checkSingleBlackFast_sound sbCell1807
  · exact checkSingleBlack_sound sbCell1808
  · exact checkSingleBlack_sound sbCell1809
  · exact checkSingleBlackFast_sound sbCell1810
  · exact checkSingleBlackFast_sound sbCell1811
  · exact checkSingleBlackFast_sound sbCell1812

end LangtonsAnt
