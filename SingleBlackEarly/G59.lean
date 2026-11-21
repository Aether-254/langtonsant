import FastCell2
import SegmentCheck
import SingleBlackEarly.C2183
import SingleBlackEarly.C2184
import SingleBlackEarly.C2185
import SingleBlackEarly.C2186
import SingleBlackEarly.C2187
import SingleBlackEarly.C2188
import SingleBlackEarly.C2189
import SingleBlackEarly.C2190
import SingleBlackEarly.C2191
import SingleBlackEarly.C2192
import SingleBlackEarly.C2193
import SingleBlackEarly.C2194
import SingleBlackEarly.C2195
import SingleBlackEarly.C2196
import SingleBlackEarly.C2197
import SingleBlackEarly.C2198
import SingleBlackEarly.C2199
import SingleBlackEarly.C2200
import SingleBlackEarly.C2201
import SingleBlackEarly.C2202
import SingleBlackEarly.C2203
import SingleBlackEarly.C2204
import SingleBlackEarly.C2205
import SingleBlackEarly.C2206
import SingleBlackEarly.C2207
import SingleBlackEarly.C2208
import SingleBlackEarly.C2209
import SingleBlackEarly.C2210
import SingleBlackEarly.C2211
import SingleBlackEarly.C2212
import SingleBlackEarly.C2213
import SingleBlackEarly.C2214

namespace LangtonsAnt

def sbGroup59 : List Point :=
  [(-89, -69), (-90, -69), (-88, -69), (-88, -70), (-89, -70), (-88, -68), (-87, -69), (-91, -65), (-92, -65), (-92, -64), (-92, -66), (-93, -66), (-93, -65), (-91, -66), (-92, -67), (-91, -69), (-92, -69), (-92, -68), (-92, -70), (-93, -70), (-93, -69), (-91, -70), (-91, -71), (-92, -71), (-90, -71), (-90, -72), (-91, -72), (-90, -70), (-89, -71), (-93, -67), (-94, -67), (-94, -66)]

theorem sbGroup59_ok : forall q, q ∈ sbGroup59 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup59, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlack_sound sbCell2183
  · exact checkSingleBlackFast_sound sbCell2184
  · exact checkSingleBlackFast_sound sbCell2185
  · exact checkSingleBlackFast_sound sbCell2186
  · exact sbCell2187
  · exact checkSingleBlackFast2_sound sbCell2188
  · exact checkSingleBlackFast_sound sbCell2189
  · exact checkSingleBlack_sound sbCell2190
  · exact checkSingleBlackFast_sound sbCell2191
  · exact checkSingleBlackFast2_sound sbCell2192
  · exact checkSingleBlackFast_sound sbCell2193
  · exact checkSingleBlackFast_sound sbCell2194
  · exact checkSingleBlackFast_sound sbCell2195
  · exact checkSingleBlackFast_sound sbCell2196
  · exact checkSingleBlackFast_sound sbCell2197
  · exact checkSingleBlackFast2_sound sbCell2198
  · exact checkSingleBlackFast2_sound sbCell2199
  · exact checkSingleBlackFast2_sound sbCell2200
  · exact checkSingleBlackFast_sound sbCell2201
  · exact checkSingleBlackFast_sound sbCell2202
  · exact checkSingleBlackFast2_sound sbCell2203
  · exact checkSingleBlackFast2_sound sbCell2204
  · exact checkSingleBlack_sound sbCell2205
  · exact checkSingleBlackFast_sound sbCell2206
  · exact checkSingleBlackFast_sound sbCell2207
  · exact checkSingleBlackFast_sound sbCell2208
  · exact checkSingleBlack_sound sbCell2209
  · exact checkSingleBlackFast2_sound sbCell2210
  · exact checkSingleBlackFast_sound sbCell2211
  · exact checkSingleBlack_sound sbCell2212
  · exact checkSingleBlackFast_sound sbCell2213
  · exact checkSingleBlackFast2_sound sbCell2214

end LangtonsAnt
