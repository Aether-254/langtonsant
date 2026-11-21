import FastCell2
import SegmentCheck
import SingleBlackEarly.C1813
import SingleBlackEarly.C1814
import SingleBlackEarly.C1815
import SingleBlackEarly.C1816
import SingleBlackEarly.C1817
import SingleBlackEarly.C1818
import SingleBlackEarly.C1819
import SingleBlackEarly.C1820
import SingleBlackEarly.C1821
import SingleBlackEarly.C1822
import SingleBlackEarly.C1823
import SingleBlackEarly.C1824
import SingleBlackEarly.C1825
import SingleBlackEarly.C1826
import SingleBlackEarly.C1827
import SingleBlackEarly.C1828
import SingleBlackEarly.C1829
import SingleBlackEarly.C1830
import SingleBlackEarly.C1831
import SingleBlackEarly.C1832
import SingleBlackEarly.C1833
import SingleBlackEarly.C1834
import SingleBlackEarly.C1835
import SingleBlackEarly.C1836
import SingleBlackEarly.C1837
import SingleBlackEarly.C1838
import SingleBlackEarly.C1839
import SingleBlackEarly.C1840
import SingleBlackEarly.C1841
import SingleBlackEarly.C1842
import SingleBlackEarly.C1843
import SingleBlackEarly.C1844
import SingleBlackEarly.C1845
import SingleBlackEarly.C1846
import SingleBlackEarly.C1847
import SingleBlackEarly.C1848
import SingleBlackEarly.C1849

namespace LangtonsAnt

def sbGroup49 : List Point :=
  [(-55, -36), (-54, -34), (-53, -35), (-57, -31), (-58, -31), (-58, -30), (-58, -32), (-59, -32), (-59, -31), (-57, -32), (-58, -33), (-57, -35), (-58, -35), (-58, -34), (-58, -36), (-59, -36), (-59, -35), (-57, -36), (-57, -37), (-58, -37), (-56, -37), (-56, -38), (-57, -38), (-56, -36), (-55, -37), (-59, -33), (-60, -33), (-60, -32), (-60, -34), (-61, -34), (-61, -33), (-59, -34), (-60, -35), (-59, -37), (-60, -37), (-60, -36), (-60, -38)]

theorem sbGroup49_ok : forall q, q ∈ sbGroup49 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup49, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sbCell1813
  · exact checkSingleBlackFast2_sound sbCell1814
  · exact checkSingleBlackFast_sound sbCell1815
  · exact checkSingleBlackFast2_sound sbCell1816
  · exact checkSingleBlackFast_sound sbCell1817
  · exact checkSingleBlackFast2_sound sbCell1818
  · exact checkSingleBlackFast_sound sbCell1819
  · exact checkSingleBlackFast2_sound sbCell1820
  · exact checkSingleBlackFast_sound sbCell1821
  · exact checkSingleBlackFast_sound sbCell1822
  · exact checkSingleBlackFast2_sound sbCell1823
  · exact checkSingleBlackFast2_sound sbCell1824
  · exact checkSingleBlackFast_sound sbCell1825
  · exact checkSingleBlack_sound sbCell1826
  · exact checkSingleBlackFast2_sound sbCell1827
  · exact checkSingleBlackFast_sound sbCell1828
  · exact checkSingleBlackFast_sound sbCell1829
  · exact checkSingleBlack_sound sbCell1830
  · exact checkSingleBlack_sound sbCell1831
  · exact checkSingleBlackFast2_sound sbCell1832
  · exact checkSingleBlackFast_sound sbCell1833
  · exact checkSingleBlackFast_sound sbCell1834
  · exact sbCell1835
  · exact checkSingleBlackFast2_sound sbCell1836
  · exact checkSingleBlackFast_sound sbCell1837
  · exact checkSingleBlackFast2_sound sbCell1838
  · exact checkSingleBlackFast_sound sbCell1839
  · exact checkSingleBlackFast2_sound sbCell1840
  · exact checkSingleBlackFast_sound sbCell1841
  · exact checkSingleBlackFast2_sound sbCell1842
  · exact checkSingleBlackFast_sound sbCell1843
  · exact checkSingleBlackFast_sound sbCell1844
  · exact checkSingleBlackFast2_sound sbCell1845
  · exact checkSingleBlackFast2_sound sbCell1846
  · exact checkSingleBlackFast_sound sbCell1847
  · exact checkSingleBlack_sound sbCell1848
  · exact checkSingleBlackFast2_sound sbCell1849

end LangtonsAnt
