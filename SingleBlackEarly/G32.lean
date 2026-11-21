import FastCell2
import SingleBlackEarly.C1184
import SingleBlackEarly.C1185
import SingleBlackEarly.C1186
import SingleBlackEarly.C1187
import SingleBlackEarly.C1188
import SingleBlackEarly.C1189
import SingleBlackEarly.C1190
import SingleBlackEarly.C1191
import SingleBlackEarly.C1192
import SingleBlackEarly.C1193
import SingleBlackEarly.C1194
import SingleBlackEarly.C1195
import SingleBlackEarly.C1196
import SingleBlackEarly.C1197
import SingleBlackEarly.C1198
import SingleBlackEarly.C1199
import SingleBlackEarly.C1200
import SingleBlackEarly.C1201
import SingleBlackEarly.C1202
import SingleBlackEarly.C1203
import SingleBlackEarly.C1204
import SingleBlackEarly.C1205
import SingleBlackEarly.C1206
import SingleBlackEarly.C1207
import SingleBlackEarly.C1208
import SingleBlackEarly.C1209
import SingleBlackEarly.C1210
import SingleBlackEarly.C1211
import SingleBlackEarly.C1212
import SingleBlackEarly.C1213
import SingleBlackEarly.C1214
import SingleBlackEarly.C1215
import SingleBlackEarly.C1216
import SingleBlackEarly.C1217
import SingleBlackEarly.C1218
import SingleBlackEarly.C1219
import SingleBlackEarly.C1220

namespace LangtonsAnt

def sbGroup32 : List Point :=
  [(26, 1), (24, 1), (24, 2), (25, 2), (24, 0), (23, 0), (23, 3), (24, 3), (25, 3), (26, 3), (26, 2), (26, 4), (27, 4), (27, 3), (25, 4), (25, 5), (26, 5), (24, 5), (24, 6), (25, 6), (24, 4), (23, 4), (23, 5), (22, 5), (22, 8), (23, 8), (23, 7), (23, 9), (24, 9), (24, 8), (22, 9), (22, 10), (23, 10), (21, 10), (21, 11), (22, 11), (21, 9)]

theorem sbGroup32_ok : forall q, q ∈ sbGroup32 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup32, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1184
  · exact checkSingleBlackFast_sound sbCell1185
  · exact checkSingleBlackFast2_sound sbCell1186
  · exact checkSingleBlackFast_sound sbCell1187
  · exact checkSingleBlackFast2_sound sbCell1188
  · exact checkSingleBlackFast_sound sbCell1189
  · exact checkSingleBlackFast_sound sbCell1190
  · exact checkSingleBlackFast_sound sbCell1191
  · exact checkSingleBlackFast2_sound sbCell1192
  · exact checkSingleBlackFast_sound sbCell1193
  · exact checkSingleBlackFast2_sound sbCell1194
  · exact checkSingleBlackFast_sound sbCell1195
  · exact checkSingleBlackFast2_sound sbCell1196
  · exact checkSingleBlackFast_sound sbCell1197
  · exact checkSingleBlackFast2_sound sbCell1198
  · exact checkSingleBlackFast_sound sbCell1199
  · exact checkSingleBlackFast2_sound sbCell1200
  · exact checkSingleBlackFast_sound sbCell1201
  · exact checkSingleBlackFast2_sound sbCell1202
  · exact checkSingleBlackFast_sound sbCell1203
  · exact checkSingleBlackFast2_sound sbCell1204
  · exact checkSingleBlackFast_sound sbCell1205
  · exact checkSingleBlackFast_sound sbCell1206
  · exact checkSingleBlackFast_sound sbCell1207
  · exact checkSingleBlackFast_sound sbCell1208
  · exact checkSingleBlackFast_sound sbCell1209
  · exact checkSingleBlackFast2_sound sbCell1210
  · exact checkSingleBlackFast_sound sbCell1211
  · exact checkSingleBlackFast_sound sbCell1212
  · exact checkSingleBlackFast_sound sbCell1213
  · exact checkSingleBlackFast2_sound sbCell1214
  · exact checkSingleBlackFast_sound sbCell1215
  · exact checkSingleBlackFast2_sound sbCell1216
  · exact checkSingleBlackFast_sound sbCell1217
  · exact checkSingleBlackFast_sound sbCell1218
  · exact checkSingleBlackFast_sound sbCell1219
  · exact checkSingleBlackFast2_sound sbCell1220

end LangtonsAnt
