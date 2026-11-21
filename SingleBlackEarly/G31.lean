import FastCell2
import SingleBlackEarly.C1147
import SingleBlackEarly.C1148
import SingleBlackEarly.C1149
import SingleBlackEarly.C1150
import SingleBlackEarly.C1151
import SingleBlackEarly.C1152
import SingleBlackEarly.C1153
import SingleBlackEarly.C1154
import SingleBlackEarly.C1155
import SingleBlackEarly.C1156
import SingleBlackEarly.C1157
import SingleBlackEarly.C1158
import SingleBlackEarly.C1159
import SingleBlackEarly.C1160
import SingleBlackEarly.C1161
import SingleBlackEarly.C1162
import SingleBlackEarly.C1163
import SingleBlackEarly.C1164
import SingleBlackEarly.C1165
import SingleBlackEarly.C1166
import SingleBlackEarly.C1167
import SingleBlackEarly.C1168
import SingleBlackEarly.C1169
import SingleBlackEarly.C1170
import SingleBlackEarly.C1171
import SingleBlackEarly.C1172
import SingleBlackEarly.C1173
import SingleBlackEarly.C1174
import SingleBlackEarly.C1175
import SingleBlackEarly.C1176
import SingleBlackEarly.C1177
import SingleBlackEarly.C1178
import SingleBlackEarly.C1179
import SingleBlackEarly.C1180
import SingleBlackEarly.C1181
import SingleBlackEarly.C1182
import SingleBlackEarly.C1183

namespace LangtonsAnt

def sbGroup31 : List Point :=
  [(18, -20), (17, -20), (17, -19), (19, -20), (19, -21), (18, -21), (20, -21), (20, -22), (19, -22), (20, -20), (26, -15), (26, -14), (27, -14), (27, -15), (26, -13), (26, -19), (26, -20), (25, -20), (27, -20), (27, -21), (26, -21), (27, -19), (28, -19), (28, -20), (28, -18), (29, -18), (29, -19), (27, -18), (23, -19), (25, -1), (26, -1), (26, -2), (26, 0), (27, 0), (27, -1), (25, 0), (25, 1)]

theorem sbGroup31_ok : forall q, q ∈ sbGroup31 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup31, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1147
  · exact checkSingleBlackFast_sound sbCell1148
  · exact checkSingleBlackFast_sound sbCell1149
  · exact checkSingleBlackFast2_sound sbCell1150
  · exact checkSingleBlackFast_sound sbCell1151
  · exact checkSingleBlackFast2_sound sbCell1152
  · exact checkSingleBlackFast_sound sbCell1153
  · exact checkSingleBlackFast2_sound sbCell1154
  · exact checkSingleBlackFast_sound sbCell1155
  · exact checkSingleBlackFast2_sound sbCell1156
  · exact checkSingleBlackFast_sound sbCell1157
  · exact checkSingleBlackFast_sound sbCell1158
  · exact checkSingleBlackFast_sound sbCell1159
  · exact checkSingleBlackFast_sound sbCell1160
  · exact checkSingleBlackFast_sound sbCell1161
  · exact checkSingleBlackFast2_sound sbCell1162
  · exact checkSingleBlackFast_sound sbCell1163
  · exact checkSingleBlackFast2_sound sbCell1164
  · exact checkSingleBlackFast_sound sbCell1165
  · exact checkSingleBlackFast_sound sbCell1166
  · exact checkSingleBlackFast_sound sbCell1167
  · exact checkSingleBlack_sound sbCell1168
  · exact checkSingleBlackFast_sound sbCell1169
  · exact checkSingleBlackFast2_sound sbCell1170
  · exact checkSingleBlackFast_sound sbCell1171
  · exact checkSingleBlackFast2_sound sbCell1172
  · exact checkSingleBlackFast_sound sbCell1173
  · exact checkSingleBlackFast2_sound sbCell1174
  · exact checkSingleBlackFast_sound sbCell1175
  · exact checkSingleBlackFast_sound sbCell1176
  · exact checkSingleBlackFast_sound sbCell1177
  · exact checkSingleBlackFast2_sound sbCell1178
  · exact checkSingleBlackFast2_sound sbCell1179
  · exact checkSingleBlackFast2_sound sbCell1180
  · exact checkSingleBlackFast_sound sbCell1181
  · exact checkSingleBlackFast2_sound sbCell1182
  · exact checkSingleBlackFast_sound sbCell1183

end LangtonsAnt
