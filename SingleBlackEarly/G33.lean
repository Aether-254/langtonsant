import FastCell2
import SingleBlackEarly.C1221
import SingleBlackEarly.C1222
import SingleBlackEarly.C1223
import SingleBlackEarly.C1224
import SingleBlackEarly.C1225
import SingleBlackEarly.C1226
import SingleBlackEarly.C1227
import SingleBlackEarly.C1228
import SingleBlackEarly.C1229
import SingleBlackEarly.C1230
import SingleBlackEarly.C1231
import SingleBlackEarly.C1232
import SingleBlackEarly.C1233
import SingleBlackEarly.C1234
import SingleBlackEarly.C1235
import SingleBlackEarly.C1236
import SingleBlackEarly.C1237
import SingleBlackEarly.C1238
import SingleBlackEarly.C1239
import SingleBlackEarly.C1240
import SingleBlackEarly.C1241
import SingleBlackEarly.C1242
import SingleBlackEarly.C1243
import SingleBlackEarly.C1244
import SingleBlackEarly.C1245
import SingleBlackEarly.C1246
import SingleBlackEarly.C1247
import SingleBlackEarly.C1248
import SingleBlackEarly.C1249
import SingleBlackEarly.C1250
import SingleBlackEarly.C1251
import SingleBlackEarly.C1252
import SingleBlackEarly.C1253
import SingleBlackEarly.C1254
import SingleBlackEarly.C1255
import SingleBlackEarly.C1256
import SingleBlackEarly.C1257

namespace LangtonsAnt

def sbGroup33 : List Point :=
  [(10, 16), (11, 16), (8, 18), (9, 18), (9, 17), (9, 19), (10, 19), (10, 18), (8, 19), (8, 20), (9, 20), (7, 20), (7, 21), (8, 21), (7, 19), (10, 17), (11, 17), (12, 17), (12, 16), (9, 16), (12, 18), (13, 18), (14, 18), (15, 18), (15, 17), (11, 18), (11, 19), (12, 19), (12, 20), (13, 20), (13, 19), (11, 20), (11, 21), (12, 21), (10, 21), (10, 22), (11, 22)]

theorem sbGroup33_ok : forall q, q ∈ sbGroup33 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup33, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1221
  · exact checkSingleBlackFast2_sound sbCell1222
  · exact checkSingleBlackFast_sound sbCell1223
  · exact checkSingleBlackFast_sound sbCell1224
  · exact checkSingleBlackFast_sound sbCell1225
  · exact checkSingleBlackFast2_sound sbCell1226
  · exact checkSingleBlackFast_sound sbCell1227
  · exact checkSingleBlackFast_sound sbCell1228
  · exact checkSingleBlackFast_sound sbCell1229
  · exact checkSingleBlackFast_sound sbCell1230
  · exact checkSingleBlackFast_sound sbCell1231
  · exact checkSingleBlackFast_sound sbCell1232
  · exact checkSingleBlackFast_sound sbCell1233
  · exact checkSingleBlackFast_sound sbCell1234
  · exact checkSingleBlackFast_sound sbCell1235
  · exact checkSingleBlackFast_sound sbCell1236
  · exact checkSingleBlackFast_sound sbCell1237
  · exact checkSingleBlackFast_sound sbCell1238
  · exact checkSingleBlackFast2_sound sbCell1239
  · exact checkSingleBlackFast_sound sbCell1240
  · exact checkSingleBlackFast_sound sbCell1241
  · exact checkSingleBlack_sound sbCell1242
  · exact checkSingleBlackFast_sound sbCell1243
  · exact checkSingleBlackFast2_sound sbCell1244
  · exact checkSingleBlackFast_sound sbCell1245
  · exact checkSingleBlackFast_sound sbCell1246
  · exact checkSingleBlackFast_sound sbCell1247
  · exact checkSingleBlackFast_sound sbCell1248
  · exact checkSingleBlackFast_sound sbCell1249
  · exact checkSingleBlackFast_sound sbCell1250
  · exact checkSingleBlackFast_sound sbCell1251
  · exact checkSingleBlackFast2_sound sbCell1252
  · exact checkSingleBlackFast_sound sbCell1253
  · exact checkSingleBlackFast2_sound sbCell1254
  · exact checkSingleBlackFast_sound sbCell1255
  · exact checkSingleBlackFast_sound sbCell1256
  · exact checkSingleBlackFast_sound sbCell1257

end LangtonsAnt
