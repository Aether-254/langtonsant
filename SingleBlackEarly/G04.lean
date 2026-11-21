import FastCell2
import SingleBlackEarly.C0148
import SingleBlackEarly.C0149
import SingleBlackEarly.C0150
import SingleBlackEarly.C0151
import SingleBlackEarly.C0152
import SingleBlackEarly.C0153
import SingleBlackEarly.C0154
import SingleBlackEarly.C0155
import SingleBlackEarly.C0156
import SingleBlackEarly.C0157
import SingleBlackEarly.C0158
import SingleBlackEarly.C0159
import SingleBlackEarly.C0160
import SingleBlackEarly.C0161
import SingleBlackEarly.C0162
import SingleBlackEarly.C0163
import SingleBlackEarly.C0164
import SingleBlackEarly.C0165
import SingleBlackEarly.C0166
import SingleBlackEarly.C0167
import SingleBlackEarly.C0168
import SingleBlackEarly.C0169
import SingleBlackEarly.C0170
import SingleBlackEarly.C0171
import SingleBlackEarly.C0172
import SingleBlackEarly.C0173
import SingleBlackEarly.C0174
import SingleBlackEarly.C0175
import SingleBlackEarly.C0176
import SingleBlackEarly.C0177
import SingleBlackEarly.C0178
import SingleBlackEarly.C0179
import SingleBlackEarly.C0180
import SingleBlackEarly.C0181
import SingleBlackEarly.C0182
import SingleBlackEarly.C0183
import SingleBlackEarly.C0184

namespace LangtonsAnt

def sbGroup04 : List Point :=
  [(3, 7), (1, 5), (0, 5), (0, 6), (1, 6), (-1, 5), (1, 7), (2, 7), (0, 7), (0, 8), (1, 8), (-1, 8), (-1, 9), (0, 9), (-1, 7), (-2, 7), (-2, 8), (-2, 6), (-5, 6), (-5, 7), (-4, 7), (-6, 7), (-6, 8), (-5, 8), (-6, 6), (-7, 6), (-7, 7), (-7, 5), (-8, 5), (-8, 6), (-6, 5), (-5, 2), (8, -1), (8, -2), (7, -2), (9, -2), (9, -3)]

theorem sbGroup04_ok : forall q, q ∈ sbGroup04 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup04, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0148
  · exact checkSingleBlackFast_sound sbCell0149
  · exact checkSingleBlackFast_sound sbCell0150
  · exact checkSingleBlackFast_sound sbCell0151
  · exact checkSingleBlackFast_sound sbCell0152
  · exact checkSingleBlackFast_sound sbCell0153
  · exact checkSingleBlackFast_sound sbCell0154
  · exact checkSingleBlackFast_sound sbCell0155
  · exact checkSingleBlackFast2_sound sbCell0156
  · exact checkSingleBlackFast_sound sbCell0157
  · exact checkSingleBlackFast_sound sbCell0158
  · exact checkSingleBlackFast_sound sbCell0159
  · exact checkSingleBlackFast_sound sbCell0160
  · exact checkSingleBlackFast_sound sbCell0161
  · exact checkSingleBlackFast_sound sbCell0162
  · exact checkSingleBlackFast_sound sbCell0163
  · exact checkSingleBlackFast_sound sbCell0164
  · exact checkSingleBlackFast_sound sbCell0165
  · exact checkSingleBlackFast2_sound sbCell0166
  · exact checkSingleBlackFast_sound sbCell0167
  · exact checkSingleBlackFast_sound sbCell0168
  · exact checkSingleBlackFast_sound sbCell0169
  · exact checkSingleBlackFast_sound sbCell0170
  · exact checkSingleBlackFast_sound sbCell0171
  · exact checkSingleBlackFast_sound sbCell0172
  · exact checkSingleBlackFast_sound sbCell0173
  · exact checkSingleBlackFast_sound sbCell0174
  · exact checkSingleBlackFast_sound sbCell0175
  · exact checkSingleBlackFast2_sound sbCell0176
  · exact checkSingleBlackFast_sound sbCell0177
  · exact checkSingleBlackFast_sound sbCell0178
  · exact checkSingleBlackFast_sound sbCell0179
  · exact checkSingleBlackFast_sound sbCell0180
  · exact checkSingleBlackFast_sound sbCell0181
  · exact checkSingleBlackFast_sound sbCell0182
  · exact checkSingleBlackFast_sound sbCell0183
  · exact checkSingleBlackFast_sound sbCell0184

end LangtonsAnt
