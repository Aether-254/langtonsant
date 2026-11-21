import FastCell2
import SegmentCheck
import SingleBlackEarly.C1924
import SingleBlackEarly.C1925
import SingleBlackEarly.C1926
import SingleBlackEarly.C1927
import SingleBlackEarly.C1928
import SingleBlackEarly.C1929
import SingleBlackEarly.C1930
import SingleBlackEarly.C1931
import SingleBlackEarly.C1932
import SingleBlackEarly.C1933
import SingleBlackEarly.C1934
import SingleBlackEarly.C1935
import SingleBlackEarly.C1936
import SingleBlackEarly.C1937
import SingleBlackEarly.C1938
import SingleBlackEarly.C1939
import SingleBlackEarly.C1940
import SingleBlackEarly.C1941
import SingleBlackEarly.C1942
import SingleBlackEarly.C1943
import SingleBlackEarly.C1944
import SingleBlackEarly.C1945
import SingleBlackEarly.C1946
import SingleBlackEarly.C1947
import SingleBlackEarly.C1948
import SingleBlackEarly.C1949
import SingleBlackEarly.C1950
import SingleBlackEarly.C1951
import SingleBlackEarly.C1952
import SingleBlackEarly.C1953
import SingleBlackEarly.C1954
import SingleBlackEarly.C1955
import SingleBlackEarly.C1956
import SingleBlackEarly.C1957
import SingleBlackEarly.C1958
import SingleBlackEarly.C1959
import SingleBlackEarly.C1960

namespace LangtonsAnt

def sbGroup52 : List Point :=
  [(-64, -44), (-63, -45), (-67, -41), (-68, -41), (-68, -40), (-68, -42), (-69, -42), (-69, -41), (-67, -42), (-68, -43), (-67, -45), (-68, -45), (-68, -44), (-68, -46), (-69, -46), (-69, -45), (-67, -46), (-67, -47), (-68, -47), (-66, -47), (-66, -48), (-67, -48), (-66, -46), (-65, -47), (-69, -43), (-70, -43), (-70, -42), (-70, -44), (-71, -44), (-71, -43), (-69, -44), (-70, -45), (-69, -47), (-70, -47), (-70, -46), (-70, -48), (-71, -48)]

theorem sbGroup52_ok : forall q, q ∈ sbGroup52 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup52, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1924
  · exact checkSingleBlackFast_sound sbCell1925
  · exact checkSingleBlackFast2_sound sbCell1926
  · exact checkSingleBlackFast_sound sbCell1927
  · exact checkSingleBlackFast2_sound sbCell1928
  · exact checkSingleBlackFast_sound sbCell1929
  · exact checkSingleBlackFast2_sound sbCell1930
  · exact checkSingleBlackFast_sound sbCell1931
  · exact checkSingleBlackFast_sound sbCell1932
  · exact checkSingleBlackFast2_sound sbCell1933
  · exact checkSingleBlackFast2_sound sbCell1934
  · exact checkSingleBlackFast_sound sbCell1935
  · exact checkSingleBlack_sound sbCell1936
  · exact checkSingleBlackFast_sound sbCell1937
  · exact checkSingleBlackFast_sound sbCell1938
  · exact checkSingleBlackFast_sound sbCell1939
  · exact checkSingleBlackFast2_sound sbCell1940
  · exact checkSingleBlack_sound sbCell1941
  · exact checkSingleBlackFast_sound sbCell1942
  · exact checkSingleBlackFast_sound sbCell1943
  · exact checkSingleBlackFast_sound sbCell1944
  · exact sbCell1945
  · exact checkSingleBlackFast2_sound sbCell1946
  · exact checkSingleBlackFast_sound sbCell1947
  · exact checkSingleBlackFast2_sound sbCell1948
  · exact checkSingleBlackFast_sound sbCell1949
  · exact checkSingleBlackFast2_sound sbCell1950
  · exact checkSingleBlackFast_sound sbCell1951
  · exact checkSingleBlackFast_sound sbCell1952
  · exact checkSingleBlackFast_sound sbCell1953
  · exact checkSingleBlackFast_sound sbCell1954
  · exact checkSingleBlackFast2_sound sbCell1955
  · exact checkSingleBlackFast2_sound sbCell1956
  · exact checkSingleBlackFast_sound sbCell1957
  · exact checkSingleBlack_sound sbCell1958
  · exact checkSingleBlackFast_sound sbCell1959
  · exact checkSingleBlackFast_sound sbCell1960

end LangtonsAnt
