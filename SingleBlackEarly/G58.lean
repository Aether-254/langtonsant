import FastCell2
import SingleBlackEarly.C2146
import SingleBlackEarly.C2147
import SingleBlackEarly.C2148
import SingleBlackEarly.C2149
import SingleBlackEarly.C2150
import SingleBlackEarly.C2151
import SingleBlackEarly.C2152
import SingleBlackEarly.C2153
import SingleBlackEarly.C2154
import SingleBlackEarly.C2155
import SingleBlackEarly.C2156
import SingleBlackEarly.C2157
import SingleBlackEarly.C2158
import SingleBlackEarly.C2159
import SingleBlackEarly.C2160
import SingleBlackEarly.C2161
import SingleBlackEarly.C2162
import SingleBlackEarly.C2163
import SingleBlackEarly.C2164
import SingleBlackEarly.C2165
import SingleBlackEarly.C2166
import SingleBlackEarly.C2167
import SingleBlackEarly.C2168
import SingleBlackEarly.C2169
import SingleBlackEarly.C2170
import SingleBlackEarly.C2171
import SingleBlackEarly.C2172
import SingleBlackEarly.C2173
import SingleBlackEarly.C2174
import SingleBlackEarly.C2175
import SingleBlackEarly.C2176
import SingleBlackEarly.C2177
import SingleBlackEarly.C2178
import SingleBlackEarly.C2179
import SingleBlackEarly.C2180
import SingleBlackEarly.C2181
import SingleBlackEarly.C2182

namespace LangtonsAnt

def sbGroup58 : List Point :=
  [(-87, -61), (-88, -61), (-88, -60), (-88, -62), (-89, -62), (-89, -61), (-87, -62), (-88, -63), (-87, -65), (-88, -65), (-88, -64), (-88, -66), (-89, -66), (-89, -65), (-87, -66), (-87, -67), (-88, -67), (-86, -67), (-86, -68), (-87, -68), (-86, -66), (-85, -67), (-89, -63), (-90, -63), (-90, -62), (-90, -64), (-91, -64), (-91, -63), (-89, -64), (-90, -65), (-89, -67), (-90, -67), (-90, -66), (-90, -68), (-91, -68), (-91, -67), (-89, -68)]

theorem sbGroup58_ok : forall q, q ∈ sbGroup58 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup58, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlack_sound sbCell2146
  · exact checkSingleBlackFast_sound sbCell2147
  · exact checkSingleBlackFast2_sound sbCell2148
  · exact checkSingleBlackFast_sound sbCell2149
  · exact checkSingleBlackFast_sound sbCell2150
  · exact checkSingleBlackFast_sound sbCell2151
  · exact checkSingleBlackFast_sound sbCell2152
  · exact checkSingleBlackFast_sound sbCell2153
  · exact checkSingleBlackFast2_sound sbCell2154
  · exact checkSingleBlackFast2_sound sbCell2155
  · exact checkSingleBlackFast2_sound sbCell2156
  · exact checkSingleBlackFast_sound sbCell2157
  · exact checkSingleBlackFast_sound sbCell2158
  · exact checkSingleBlackFast2_sound sbCell2159
  · exact checkSingleBlackFast2_sound sbCell2160
  · exact checkSingleBlack_sound sbCell2161
  · exact checkSingleBlackFast_sound sbCell2162
  · exact checkSingleBlackFast_sound sbCell2163
  · exact checkSingleBlackFast_sound sbCell2164
  · exact checkSingleBlackFast_sound sbCell2165
  · exact checkSingleBlackFast2_sound sbCell2166
  · exact checkSingleBlackFast_sound sbCell2167
  · exact checkSingleBlack_sound sbCell2168
  · exact checkSingleBlackFast_sound sbCell2169
  · exact checkSingleBlackFast2_sound sbCell2170
  · exact checkSingleBlackFast_sound sbCell2171
  · exact checkSingleBlackFast_sound sbCell2172
  · exact checkSingleBlackFast_sound sbCell2173
  · exact checkSingleBlackFast_sound sbCell2174
  · exact checkSingleBlackFast2_sound sbCell2175
  · exact checkSingleBlackFast2_sound sbCell2176
  · exact checkSingleBlackFast2_sound sbCell2177
  · exact checkSingleBlackFast2_sound sbCell2178
  · exact checkSingleBlackFast_sound sbCell2179
  · exact checkSingleBlackFast_sound sbCell2180
  · exact checkSingleBlackFast2_sound sbCell2181
  · exact checkSingleBlackFast2_sound sbCell2182

end LangtonsAnt
