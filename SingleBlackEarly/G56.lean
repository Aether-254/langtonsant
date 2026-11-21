import FastCell2
import SingleBlackEarly.C2072
import SingleBlackEarly.C2073
import SingleBlackEarly.C2074
import SingleBlackEarly.C2075
import SingleBlackEarly.C2076
import SingleBlackEarly.C2077
import SingleBlackEarly.C2078
import SingleBlackEarly.C2079
import SingleBlackEarly.C2080
import SingleBlackEarly.C2081
import SingleBlackEarly.C2082
import SingleBlackEarly.C2083
import SingleBlackEarly.C2084
import SingleBlackEarly.C2085
import SingleBlackEarly.C2086
import SingleBlackEarly.C2087
import SingleBlackEarly.C2088
import SingleBlackEarly.C2089
import SingleBlackEarly.C2090
import SingleBlackEarly.C2091
import SingleBlackEarly.C2092
import SingleBlackEarly.C2093
import SingleBlackEarly.C2094
import SingleBlackEarly.C2095
import SingleBlackEarly.C2096
import SingleBlackEarly.C2097
import SingleBlackEarly.C2098
import SingleBlackEarly.C2099
import SingleBlackEarly.C2100
import SingleBlackEarly.C2101
import SingleBlackEarly.C2102
import SingleBlackEarly.C2103
import SingleBlackEarly.C2104
import SingleBlackEarly.C2105
import SingleBlackEarly.C2106
import SingleBlackEarly.C2107
import SingleBlackEarly.C2108

namespace LangtonsAnt

def sbGroup56 : List Point :=
  [(-79, -58), (-79, -59), (-80, -59), (-78, -59), (-78, -60), (-79, -60), (-78, -58), (-77, -59), (-81, -55), (-82, -55), (-82, -54), (-82, -56), (-83, -56), (-83, -55), (-81, -56), (-82, -57), (-81, -59), (-82, -59), (-82, -58), (-82, -60), (-83, -60), (-83, -59), (-81, -60), (-81, -61), (-82, -61), (-80, -61), (-80, -62), (-81, -62), (-80, -60), (-79, -61), (-83, -57), (-84, -57), (-84, -56), (-84, -58), (-85, -58), (-85, -57), (-83, -58)]

theorem sbGroup56_ok : forall q, q ∈ sbGroup56 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup56, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell2072
  · exact checkSingleBlack_sound sbCell2073
  · exact checkSingleBlackFast_sound sbCell2074
  · exact checkSingleBlackFast_sound sbCell2075
  · exact checkSingleBlackFast_sound sbCell2076
  · exact checkSingleBlackFast_sound sbCell2077
  · exact checkSingleBlackFast2_sound sbCell2078
  · exact checkSingleBlackFast_sound sbCell2079
  · exact checkSingleBlack_sound sbCell2080
  · exact checkSingleBlackFast_sound sbCell2081
  · exact checkSingleBlackFast2_sound sbCell2082
  · exact checkSingleBlackFast_sound sbCell2083
  · exact checkSingleBlackFast_sound sbCell2084
  · exact checkSingleBlackFast_sound sbCell2085
  · exact checkSingleBlackFast_sound sbCell2086
  · exact checkSingleBlackFast2_sound sbCell2087
  · exact checkSingleBlackFast2_sound sbCell2088
  · exact checkSingleBlackFast2_sound sbCell2089
  · exact checkSingleBlackFast2_sound sbCell2090
  · exact checkSingleBlackFast_sound sbCell2091
  · exact checkSingleBlackFast_sound sbCell2092
  · exact checkSingleBlackFast2_sound sbCell2093
  · exact checkSingleBlackFast2_sound sbCell2094
  · exact checkSingleBlack_sound sbCell2095
  · exact checkSingleBlackFast_sound sbCell2096
  · exact checkSingleBlackFast_sound sbCell2097
  · exact checkSingleBlackFast_sound sbCell2098
  · exact checkSingleBlack_sound sbCell2099
  · exact checkSingleBlackFast2_sound sbCell2100
  · exact checkSingleBlackFast_sound sbCell2101
  · exact checkSingleBlack_sound sbCell2102
  · exact checkSingleBlackFast_sound sbCell2103
  · exact checkSingleBlackFast2_sound sbCell2104
  · exact checkSingleBlackFast_sound sbCell2105
  · exact checkSingleBlackFast_sound sbCell2106
  · exact checkSingleBlackFast_sound sbCell2107
  · exact checkSingleBlackFast_sound sbCell2108

end LangtonsAnt
