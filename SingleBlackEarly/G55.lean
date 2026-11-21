import FastCell2
import SegmentCheck
import SingleBlackEarly.C2035
import SingleBlackEarly.C2036
import SingleBlackEarly.C2037
import SingleBlackEarly.C2038
import SingleBlackEarly.C2039
import SingleBlackEarly.C2040
import SingleBlackEarly.C2041
import SingleBlackEarly.C2042
import SingleBlackEarly.C2043
import SingleBlackEarly.C2044
import SingleBlackEarly.C2045
import SingleBlackEarly.C2046
import SingleBlackEarly.C2047
import SingleBlackEarly.C2048
import SingleBlackEarly.C2049
import SingleBlackEarly.C2050
import SingleBlackEarly.C2051
import SingleBlackEarly.C2052
import SingleBlackEarly.C2053
import SingleBlackEarly.C2054
import SingleBlackEarly.C2055
import SingleBlackEarly.C2056
import SingleBlackEarly.C2057
import SingleBlackEarly.C2058
import SingleBlackEarly.C2059
import SingleBlackEarly.C2060
import SingleBlackEarly.C2061
import SingleBlackEarly.C2062
import SingleBlackEarly.C2063
import SingleBlackEarly.C2064
import SingleBlackEarly.C2065
import SingleBlackEarly.C2066
import SingleBlackEarly.C2067
import SingleBlackEarly.C2068
import SingleBlackEarly.C2069
import SingleBlackEarly.C2070
import SingleBlackEarly.C2071

namespace LangtonsAnt

def sbGroup55 : List Point :=
  [(-73, -55), (-77, -51), (-78, -51), (-78, -50), (-78, -52), (-79, -52), (-79, -51), (-77, -52), (-78, -53), (-77, -55), (-78, -55), (-78, -54), (-78, -56), (-79, -56), (-79, -55), (-77, -56), (-77, -57), (-78, -57), (-76, -57), (-76, -58), (-77, -58), (-76, -56), (-75, -57), (-79, -53), (-80, -53), (-80, -52), (-80, -54), (-81, -54), (-81, -53), (-79, -54), (-80, -55), (-79, -57), (-80, -57), (-80, -56), (-80, -58), (-81, -58), (-81, -57)]

theorem sbGroup55_ok : forall q, q ∈ sbGroup55 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup55, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell2035
  · exact checkSingleBlack_sound sbCell2036
  · exact checkSingleBlackFast_sound sbCell2037
  · exact checkSingleBlackFast2_sound sbCell2038
  · exact checkSingleBlackFast_sound sbCell2039
  · exact checkSingleBlackFast_sound sbCell2040
  · exact checkSingleBlackFast_sound sbCell2041
  · exact checkSingleBlackFast_sound sbCell2042
  · exact checkSingleBlackFast2_sound sbCell2043
  · exact checkSingleBlackFast2_sound sbCell2044
  · exact checkSingleBlackFast2_sound sbCell2045
  · exact checkSingleBlackFast2_sound sbCell2046
  · exact checkSingleBlackFast2_sound sbCell2047
  · exact checkSingleBlackFast_sound sbCell2048
  · exact checkSingleBlackFast2_sound sbCell2049
  · exact checkSingleBlackFast2_sound sbCell2050
  · exact checkSingleBlack_sound sbCell2051
  · exact checkSingleBlackFast_sound sbCell2052
  · exact checkSingleBlackFast_sound sbCell2053
  · exact checkSingleBlackFast_sound sbCell2054
  · exact sbCell2055
  · exact checkSingleBlackFast2_sound sbCell2056
  · exact checkSingleBlackFast_sound sbCell2057
  · exact checkSingleBlack_sound sbCell2058
  · exact checkSingleBlackFast_sound sbCell2059
  · exact checkSingleBlackFast2_sound sbCell2060
  · exact checkSingleBlackFast_sound sbCell2061
  · exact checkSingleBlackFast_sound sbCell2062
  · exact checkSingleBlackFast_sound sbCell2063
  · exact checkSingleBlackFast_sound sbCell2064
  · exact checkSingleBlackFast2_sound sbCell2065
  · exact checkSingleBlackFast2_sound sbCell2066
  · exact checkSingleBlackFast2_sound sbCell2067
  · exact checkSingleBlackFast2_sound sbCell2068
  · exact checkSingleBlackFast_sound sbCell2069
  · exact checkSingleBlackFast_sound sbCell2070
  · exact checkSingleBlackFast2_sound sbCell2071

end LangtonsAnt
