import FastCell2
import SingleBlackEarly.C1258
import SingleBlackEarly.C1259
import SingleBlackEarly.C1260
import SingleBlackEarly.C1261
import SingleBlackEarly.C1262
import SingleBlackEarly.C1263
import SingleBlackEarly.C1264
import SingleBlackEarly.C1265
import SingleBlackEarly.C1266
import SingleBlackEarly.C1267
import SingleBlackEarly.C1268
import SingleBlackEarly.C1269
import SingleBlackEarly.C1270
import SingleBlackEarly.C1271
import SingleBlackEarly.C1272
import SingleBlackEarly.C1273
import SingleBlackEarly.C1274
import SingleBlackEarly.C1275
import SingleBlackEarly.C1276
import SingleBlackEarly.C1277
import SingleBlackEarly.C1278
import SingleBlackEarly.C1279
import SingleBlackEarly.C1280
import SingleBlackEarly.C1281
import SingleBlackEarly.C1282
import SingleBlackEarly.C1283
import SingleBlackEarly.C1284
import SingleBlackEarly.C1285
import SingleBlackEarly.C1286
import SingleBlackEarly.C1287
import SingleBlackEarly.C1288
import SingleBlackEarly.C1289
import SingleBlackEarly.C1290
import SingleBlackEarly.C1291
import SingleBlackEarly.C1292
import SingleBlackEarly.C1293
import SingleBlackEarly.C1294

namespace LangtonsAnt

def sbGroup34 : List Point :=
  [(10, 20), (6, 21), (6, 22), (7, 22), (6, 20), (5, 20), (5, 21), (4, 21), (4, 22), (5, 22), (4, 20), (3, 20), (3, 21), (2, 21), (2, 22), (3, 22), (2, 20), (1, 20), (1, 21), (0, 21), (0, 22), (1, 22), (0, 20), (-1, 20), (-1, 21), (-2, 21), (-2, 22), (-1, 22), (-2, 20), (-3, 20), (-3, 21), (-4, 21), (-4, 22), (-3, 22), (-4, 20), (-5, 21), (-7, 20)]

theorem sbGroup34_ok : forall q, q ∈ sbGroup34 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup34, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1258
  · exact checkSingleBlackFast_sound sbCell1259
  · exact checkSingleBlackFast2_sound sbCell1260
  · exact checkSingleBlackFast_sound sbCell1261
  · exact checkSingleBlackFast_sound sbCell1262
  · exact checkSingleBlackFast_sound sbCell1263
  · exact checkSingleBlackFast_sound sbCell1264
  · exact checkSingleBlackFast_sound sbCell1265
  · exact checkSingleBlackFast_sound sbCell1266
  · exact checkSingleBlackFast_sound sbCell1267
  · exact checkSingleBlackFast_sound sbCell1268
  · exact checkSingleBlackFast_sound sbCell1269
  · exact checkSingleBlackFast_sound sbCell1270
  · exact checkSingleBlackFast_sound sbCell1271
  · exact checkSingleBlackFast_sound sbCell1272
  · exact checkSingleBlackFast_sound sbCell1273
  · exact checkSingleBlackFast_sound sbCell1274
  · exact checkSingleBlackFast_sound sbCell1275
  · exact checkSingleBlackFast_sound sbCell1276
  · exact checkSingleBlackFast_sound sbCell1277
  · exact checkSingleBlackFast_sound sbCell1278
  · exact checkSingleBlackFast_sound sbCell1279
  · exact checkSingleBlackFast_sound sbCell1280
  · exact checkSingleBlackFast_sound sbCell1281
  · exact checkSingleBlackFast_sound sbCell1282
  · exact checkSingleBlackFast_sound sbCell1283
  · exact checkSingleBlackFast_sound sbCell1284
  · exact checkSingleBlackFast_sound sbCell1285
  · exact checkSingleBlackFast_sound sbCell1286
  · exact checkSingleBlackFast_sound sbCell1287
  · exact checkSingleBlackFast_sound sbCell1288
  · exact checkSingleBlackFast_sound sbCell1289
  · exact checkSingleBlackFast2_sound sbCell1290
  · exact checkSingleBlackFast_sound sbCell1291
  · exact checkSingleBlackFast2_sound sbCell1292
  · exact checkSingleBlackFast_sound sbCell1293
  · exact checkSingleBlackFast_sound sbCell1294

end LangtonsAnt
