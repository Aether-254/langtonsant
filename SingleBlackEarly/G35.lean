import FastCell2
import SingleBlackEarly.C1295
import SingleBlackEarly.C1296
import SingleBlackEarly.C1297
import SingleBlackEarly.C1298
import SingleBlackEarly.C1299
import SingleBlackEarly.C1300
import SingleBlackEarly.C1301
import SingleBlackEarly.C1302
import SingleBlackEarly.C1303
import SingleBlackEarly.C1304
import SingleBlackEarly.C1305
import SingleBlackEarly.C1306
import SingleBlackEarly.C1307
import SingleBlackEarly.C1308
import SingleBlackEarly.C1309
import SingleBlackEarly.C1310
import SingleBlackEarly.C1311
import SingleBlackEarly.C1312
import SingleBlackEarly.C1313
import SingleBlackEarly.C1314
import SingleBlackEarly.C1315
import SingleBlackEarly.C1316
import SingleBlackEarly.C1317
import SingleBlackEarly.C1318
import SingleBlackEarly.C1319
import SingleBlackEarly.C1320
import SingleBlackEarly.C1321
import SingleBlackEarly.C1322
import SingleBlackEarly.C1323
import SingleBlackEarly.C1324
import SingleBlackEarly.C1325
import SingleBlackEarly.C1326
import SingleBlackEarly.C1327
import SingleBlackEarly.C1328
import SingleBlackEarly.C1329
import SingleBlackEarly.C1330
import SingleBlackEarly.C1331

namespace LangtonsAnt

def sbGroup35 : List Point :=
  [(-7, 21), (-6, 21), (-8, 21), (-8, 22), (-7, 22), (-8, 20), (-9, 20), (-9, 21), (-9, 19), (-10, 19), (-10, 20), (-8, 19), (-8, 16), (-9, 16), (-9, 17), (-10, 17), (-10, 18), (-9, 18), (-10, 16), (-11, 16), (-11, 17), (-11, 15), (-12, 15), (-12, 16), (-10, 15), (-10, 14), (-13, 14), (-13, 15), (-13, 16), (-13, 17), (-12, 17), (-14, 17), (-14, 18), (-13, 18), (-14, 16), (-15, 16), (-15, 17)]

theorem sbGroup35_ok : forall q, q ∈ sbGroup35 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup35, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1295
  · exact checkSingleBlackFast2_sound sbCell1296
  · exact checkSingleBlackFast_sound sbCell1297
  · exact checkSingleBlackFast_sound sbCell1298
  · exact checkSingleBlackFast_sound sbCell1299
  · exact checkSingleBlackFast2_sound sbCell1300
  · exact checkSingleBlackFast_sound sbCell1301
  · exact checkSingleBlack_sound sbCell1302
  · exact checkSingleBlackFast_sound sbCell1303
  · exact checkSingleBlackFast2_sound sbCell1304
  · exact checkSingleBlackFast_sound sbCell1305
  · exact checkSingleBlackFast2_sound sbCell1306
  · exact checkSingleBlackFast_sound sbCell1307
  · exact checkSingleBlackFast_sound sbCell1308
  · exact checkSingleBlackFast_sound sbCell1309
  · exact checkSingleBlackFast2_sound sbCell1310
  · exact checkSingleBlackFast_sound sbCell1311
  · exact checkSingleBlackFast2_sound sbCell1312
  · exact checkSingleBlackFast_sound sbCell1313
  · exact checkSingleBlackFast2_sound sbCell1314
  · exact checkSingleBlackFast_sound sbCell1315
  · exact checkSingleBlack_sound sbCell1316
  · exact checkSingleBlackFast_sound sbCell1317
  · exact checkSingleBlack_sound sbCell1318
  · exact checkSingleBlackFast_sound sbCell1319
  · exact checkSingleBlack_sound sbCell1320
  · exact checkSingleBlackFast2_sound sbCell1321
  · exact checkSingleBlackFast2_sound sbCell1322
  · exact checkSingleBlackFast_sound sbCell1323
  · exact checkSingleBlackFast_sound sbCell1324
  · exact checkSingleBlackFast_sound sbCell1325
  · exact checkSingleBlackFast2_sound sbCell1326
  · exact checkSingleBlackFast_sound sbCell1327
  · exact checkSingleBlackFast2_sound sbCell1328
  · exact checkSingleBlackFast2_sound sbCell1329
  · exact checkSingleBlackFast_sound sbCell1330
  · exact checkSingleBlackFast_sound sbCell1331

end LangtonsAnt
