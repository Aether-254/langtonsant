import FastCell2
import SegmentCheck
import SingleBlackEarly.C1887
import SingleBlackEarly.C1888
import SingleBlackEarly.C1889
import SingleBlackEarly.C1890
import SingleBlackEarly.C1891
import SingleBlackEarly.C1892
import SingleBlackEarly.C1893
import SingleBlackEarly.C1894
import SingleBlackEarly.C1895
import SingleBlackEarly.C1896
import SingleBlackEarly.C1897
import SingleBlackEarly.C1898
import SingleBlackEarly.C1899
import SingleBlackEarly.C1900
import SingleBlackEarly.C1901
import SingleBlackEarly.C1902
import SingleBlackEarly.C1903
import SingleBlackEarly.C1904
import SingleBlackEarly.C1905
import SingleBlackEarly.C1906
import SingleBlackEarly.C1907
import SingleBlackEarly.C1908
import SingleBlackEarly.C1909
import SingleBlackEarly.C1910
import SingleBlackEarly.C1911
import SingleBlackEarly.C1912
import SingleBlackEarly.C1913
import SingleBlackEarly.C1914
import SingleBlackEarly.C1915
import SingleBlackEarly.C1916
import SingleBlackEarly.C1917
import SingleBlackEarly.C1918
import SingleBlackEarly.C1919
import SingleBlackEarly.C1920
import SingleBlackEarly.C1921
import SingleBlackEarly.C1922
import SingleBlackEarly.C1923

namespace LangtonsAnt

def sbGroup51 : List Point :=
  [(-65, -37), (-63, -38), (-64, -39), (-63, -41), (-64, -41), (-64, -40), (-64, -42), (-65, -42), (-65, -41), (-63, -42), (-63, -43), (-64, -43), (-62, -43), (-62, -44), (-63, -44), (-62, -42), (-61, -43), (-65, -39), (-66, -39), (-66, -38), (-66, -40), (-67, -40), (-67, -39), (-65, -40), (-66, -41), (-65, -43), (-66, -43), (-66, -42), (-66, -44), (-67, -44), (-67, -43), (-65, -44), (-65, -45), (-66, -45), (-64, -45), (-64, -46), (-65, -46)]

theorem sbGroup51_ok : forall q, q ∈ sbGroup51 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup51, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1887
  · exact checkSingleBlackFast_sound sbCell1888
  · exact checkSingleBlack_sound sbCell1889
  · exact checkSingleBlackFast2_sound sbCell1890
  · exact checkSingleBlackFast_sound sbCell1891
  · exact checkSingleBlack_sound sbCell1892
  · exact checkSingleBlackFast2_sound sbCell1893
  · exact checkSingleBlackFast_sound sbCell1894
  · exact checkSingleBlackFast_sound sbCell1895
  · exact checkSingleBlack_sound sbCell1896
  · exact checkSingleBlack_sound sbCell1897
  · exact checkSingleBlackFast_sound sbCell1898
  · exact checkSingleBlackFast_sound sbCell1899
  · exact checkSingleBlackFast_sound sbCell1900
  · exact sbCell1901
  · exact checkSingleBlackFast2_sound sbCell1902
  · exact checkSingleBlackFast_sound sbCell1903
  · exact checkSingleBlack_sound sbCell1904
  · exact checkSingleBlackFast2_sound sbCell1905
  · exact checkSingleBlackFast2_sound sbCell1906
  · exact checkSingleBlackFast_sound sbCell1907
  · exact checkSingleBlackFast2_sound sbCell1908
  · exact checkSingleBlackFast_sound sbCell1909
  · exact checkSingleBlackFast_sound sbCell1910
  · exact checkSingleBlackFast2_sound sbCell1911
  · exact checkSingleBlackFast2_sound sbCell1912
  · exact checkSingleBlackFast_sound sbCell1913
  · exact checkSingleBlack_sound sbCell1914
  · exact checkSingleBlackFast_sound sbCell1915
  · exact checkSingleBlackFast_sound sbCell1916
  · exact checkSingleBlackFast_sound sbCell1917
  · exact checkSingleBlackFast2_sound sbCell1918
  · exact checkSingleBlack_sound sbCell1919
  · exact checkSingleBlackFast_sound sbCell1920
  · exact checkSingleBlackFast_sound sbCell1921
  · exact checkSingleBlackFast_sound sbCell1922
  · exact sbCell1923

end LangtonsAnt
