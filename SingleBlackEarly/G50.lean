import FastCell2
import SegmentCheck
import SingleBlackEarly.C1850
import SingleBlackEarly.C1851
import SingleBlackEarly.C1852
import SingleBlackEarly.C1853
import SingleBlackEarly.C1854
import SingleBlackEarly.C1855
import SingleBlackEarly.C1856
import SingleBlackEarly.C1857
import SingleBlackEarly.C1858
import SingleBlackEarly.C1859
import SingleBlackEarly.C1860
import SingleBlackEarly.C1861
import SingleBlackEarly.C1862
import SingleBlackEarly.C1863
import SingleBlackEarly.C1864
import SingleBlackEarly.C1865
import SingleBlackEarly.C1866
import SingleBlackEarly.C1867
import SingleBlackEarly.C1868
import SingleBlackEarly.C1869
import SingleBlackEarly.C1870
import SingleBlackEarly.C1871
import SingleBlackEarly.C1872
import SingleBlackEarly.C1873
import SingleBlackEarly.C1874
import SingleBlackEarly.C1875
import SingleBlackEarly.C1876
import SingleBlackEarly.C1877
import SingleBlackEarly.C1878
import SingleBlackEarly.C1879
import SingleBlackEarly.C1880
import SingleBlackEarly.C1881
import SingleBlackEarly.C1882
import SingleBlackEarly.C1883
import SingleBlackEarly.C1884
import SingleBlackEarly.C1885
import SingleBlackEarly.C1886

namespace LangtonsAnt

def sbGroup50 : List Point :=
  [(-61, -38), (-61, -37), (-59, -38), (-59, -39), (-60, -39), (-58, -39), (-58, -40), (-59, -40), (-58, -38), (-57, -39), (-61, -35), (-62, -35), (-62, -34), (-62, -36), (-63, -36), (-63, -35), (-61, -36), (-62, -37), (-61, -39), (-62, -39), (-62, -38), (-62, -40), (-63, -40), (-63, -39), (-61, -40), (-61, -41), (-62, -41), (-60, -41), (-60, -42), (-61, -42), (-60, -40), (-59, -41), (-63, -37), (-64, -37), (-64, -36), (-64, -38), (-65, -38)]

theorem sbGroup50_ok : forall q, q ∈ sbGroup50 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup50, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1850
  · exact checkSingleBlackFast_sound sbCell1851
  · exact checkSingleBlack_sound sbCell1852
  · exact checkSingleBlack_sound sbCell1853
  · exact checkSingleBlackFast_sound sbCell1854
  · exact checkSingleBlackFast_sound sbCell1855
  · exact checkSingleBlackFast_sound sbCell1856
  · exact sbCell1857
  · exact checkSingleBlackFast2_sound sbCell1858
  · exact checkSingleBlackFast_sound sbCell1859
  · exact checkSingleBlackFast2_sound sbCell1860
  · exact checkSingleBlackFast_sound sbCell1861
  · exact checkSingleBlackFast2_sound sbCell1862
  · exact checkSingleBlackFast_sound sbCell1863
  · exact checkSingleBlackFast2_sound sbCell1864
  · exact checkSingleBlackFast_sound sbCell1865
  · exact checkSingleBlackFast_sound sbCell1866
  · exact checkSingleBlackFast2_sound sbCell1867
  · exact checkSingleBlackFast2_sound sbCell1868
  · exact checkSingleBlackFast_sound sbCell1869
  · exact checkSingleBlack_sound sbCell1870
  · exact checkSingleBlackFast2_sound sbCell1871
  · exact checkSingleBlackFast_sound sbCell1872
  · exact checkSingleBlackFast_sound sbCell1873
  · exact checkSingleBlack_sound sbCell1874
  · exact checkSingleBlack_sound sbCell1875
  · exact checkSingleBlackFast_sound sbCell1876
  · exact checkSingleBlackFast_sound sbCell1877
  · exact checkSingleBlackFast_sound sbCell1878
  · exact sbCell1879
  · exact checkSingleBlackFast2_sound sbCell1880
  · exact checkSingleBlackFast_sound sbCell1881
  · exact checkSingleBlackFast2_sound sbCell1882
  · exact checkSingleBlackFast_sound sbCell1883
  · exact checkSingleBlackFast2_sound sbCell1884
  · exact checkSingleBlackFast_sound sbCell1885
  · exact checkSingleBlackFast2_sound sbCell1886

end LangtonsAnt
