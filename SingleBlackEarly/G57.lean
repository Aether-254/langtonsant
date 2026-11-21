import FastCell2
import SingleBlackEarly.C2109
import SingleBlackEarly.C2110
import SingleBlackEarly.C2111
import SingleBlackEarly.C2112
import SingleBlackEarly.C2113
import SingleBlackEarly.C2114
import SingleBlackEarly.C2115
import SingleBlackEarly.C2116
import SingleBlackEarly.C2117
import SingleBlackEarly.C2118
import SingleBlackEarly.C2119
import SingleBlackEarly.C2120
import SingleBlackEarly.C2121
import SingleBlackEarly.C2122
import SingleBlackEarly.C2123
import SingleBlackEarly.C2124
import SingleBlackEarly.C2125
import SingleBlackEarly.C2126
import SingleBlackEarly.C2127
import SingleBlackEarly.C2128
import SingleBlackEarly.C2129
import SingleBlackEarly.C2130
import SingleBlackEarly.C2131
import SingleBlackEarly.C2132
import SingleBlackEarly.C2133
import SingleBlackEarly.C2134
import SingleBlackEarly.C2135
import SingleBlackEarly.C2136
import SingleBlackEarly.C2137
import SingleBlackEarly.C2138
import SingleBlackEarly.C2139
import SingleBlackEarly.C2140
import SingleBlackEarly.C2141
import SingleBlackEarly.C2142
import SingleBlackEarly.C2143
import SingleBlackEarly.C2144
import SingleBlackEarly.C2145

namespace LangtonsAnt

def sbGroup57 : List Point :=
  [(-84, -59), (-83, -61), (-84, -61), (-84, -60), (-84, -62), (-85, -62), (-85, -61), (-83, -62), (-83, -63), (-84, -63), (-82, -63), (-82, -64), (-83, -64), (-82, -62), (-81, -63), (-85, -59), (-86, -59), (-86, -58), (-86, -60), (-87, -60), (-87, -59), (-85, -60), (-86, -61), (-85, -63), (-86, -63), (-86, -62), (-86, -64), (-87, -64), (-87, -63), (-85, -64), (-85, -65), (-86, -65), (-84, -65), (-84, -66), (-85, -66), (-84, -64), (-83, -65)]

theorem sbGroup57_ok : forall q, q ∈ sbGroup57 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup57, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell2109
  · exact checkSingleBlackFast2_sound sbCell2110
  · exact checkSingleBlackFast2_sound sbCell2111
  · exact checkSingleBlackFast2_sound sbCell2112
  · exact checkSingleBlackFast_sound sbCell2113
  · exact checkSingleBlackFast_sound sbCell2114
  · exact checkSingleBlackFast2_sound sbCell2115
  · exact checkSingleBlackFast2_sound sbCell2116
  · exact checkSingleBlack_sound sbCell2117
  · exact checkSingleBlackFast_sound sbCell2118
  · exact checkSingleBlackFast_sound sbCell2119
  · exact checkSingleBlackFast_sound sbCell2120
  · exact checkSingleBlack_sound sbCell2121
  · exact checkSingleBlackFast2_sound sbCell2122
  · exact checkSingleBlackFast_sound sbCell2123
  · exact checkSingleBlack_sound sbCell2124
  · exact checkSingleBlackFast_sound sbCell2125
  · exact checkSingleBlackFast2_sound sbCell2126
  · exact checkSingleBlackFast_sound sbCell2127
  · exact checkSingleBlackFast_sound sbCell2128
  · exact checkSingleBlackFast_sound sbCell2129
  · exact checkSingleBlackFast_sound sbCell2130
  · exact checkSingleBlackFast_sound sbCell2131
  · exact checkSingleBlackFast2_sound sbCell2132
  · exact checkSingleBlackFast2_sound sbCell2133
  · exact checkSingleBlackFast2_sound sbCell2134
  · exact checkSingleBlackFast_sound sbCell2135
  · exact checkSingleBlackFast_sound sbCell2136
  · exact checkSingleBlackFast2_sound sbCell2137
  · exact checkSingleBlackFast2_sound sbCell2138
  · exact checkSingleBlack_sound sbCell2139
  · exact checkSingleBlackFast_sound sbCell2140
  · exact checkSingleBlackFast_sound sbCell2141
  · exact checkSingleBlackFast_sound sbCell2142
  · exact checkSingleBlack_sound sbCell2143
  · exact checkSingleBlackFast2_sound sbCell2144
  · exact checkSingleBlackFast_sound sbCell2145

end LangtonsAnt
