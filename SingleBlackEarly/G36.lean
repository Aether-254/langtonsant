import FastCell2
import SingleBlackEarly.C1332
import SingleBlackEarly.C1333
import SingleBlackEarly.C1334
import SingleBlackEarly.C1335
import SingleBlackEarly.C1336
import SingleBlackEarly.C1337
import SingleBlackEarly.C1338
import SingleBlackEarly.C1339
import SingleBlackEarly.C1340
import SingleBlackEarly.C1341
import SingleBlackEarly.C1342
import SingleBlackEarly.C1343
import SingleBlackEarly.C1344
import SingleBlackEarly.C1345
import SingleBlackEarly.C1346
import SingleBlackEarly.C1347
import SingleBlackEarly.C1348
import SingleBlackEarly.C1349
import SingleBlackEarly.C1350
import SingleBlackEarly.C1351
import SingleBlackEarly.C1352
import SingleBlackEarly.C1353
import SingleBlackEarly.C1354
import SingleBlackEarly.C1355
import SingleBlackEarly.C1356
import SingleBlackEarly.C1357
import SingleBlackEarly.C1358
import SingleBlackEarly.C1359
import SingleBlackEarly.C1360
import SingleBlackEarly.C1361
import SingleBlackEarly.C1362
import SingleBlackEarly.C1363
import SingleBlackEarly.C1364
import SingleBlackEarly.C1365
import SingleBlackEarly.C1366
import SingleBlackEarly.C1367
import SingleBlackEarly.C1368

namespace LangtonsAnt

def sbGroup36 : List Point :=
  [(-15, 15), (-16, 15), (-16, 16), (-14, 15), (-14, 14), (-15, 14), (-15, 13), (-16, 13), (-16, 14), (-14, 13), (-15, 12), (-15, 11), (-16, 11), (-16, 12), (-16, 10), (-17, 10), (-17, 11), (-15, 10), (-15, 7), (-16, 7), (-16, 8), (-16, 6), (-17, 6), (-17, 7), (-15, 6), (-15, 5), (-16, 5), (-14, 5), (-14, 4), (-15, 4), (-14, 6), (-17, 14), (-17, 15), (-17, 16), (-17, 17), (-16, 17), (-17, 13)]

theorem sbGroup36_ok : forall q, q ∈ sbGroup36 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup36, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1332
  · exact checkSingleBlackFast_sound sbCell1333
  · exact checkSingleBlack_sound sbCell1334
  · exact checkSingleBlackFast_sound sbCell1335
  · exact checkSingleBlackFast2_sound sbCell1336
  · exact checkSingleBlackFast_sound sbCell1337
  · exact checkSingleBlackFast2_sound sbCell1338
  · exact checkSingleBlackFast_sound sbCell1339
  · exact checkSingleBlackFast_sound sbCell1340
  · exact checkSingleBlackFast_sound sbCell1341
  · exact checkSingleBlackFast2_sound sbCell1342
  · exact checkSingleBlackFast2_sound sbCell1343
  · exact checkSingleBlackFast2_sound sbCell1344
  · exact checkSingleBlackFast_sound sbCell1345
  · exact checkSingleBlackFast_sound sbCell1346
  · exact checkSingleBlackFast2_sound sbCell1347
  · exact checkSingleBlackFast2_sound sbCell1348
  · exact checkSingleBlackFast_sound sbCell1349
  · exact checkSingleBlackFast2_sound sbCell1350
  · exact checkSingleBlackFast_sound sbCell1351
  · exact checkSingleBlackFast2_sound sbCell1352
  · exact checkSingleBlackFast_sound sbCell1353
  · exact checkSingleBlackFast2_sound sbCell1354
  · exact checkSingleBlackFast_sound sbCell1355
  · exact checkSingleBlackFast2_sound sbCell1356
  · exact checkSingleBlackFast_sound sbCell1357
  · exact checkSingleBlackFast_sound sbCell1358
  · exact checkSingleBlackFast_sound sbCell1359
  · exact checkSingleBlackFast2_sound sbCell1360
  · exact checkSingleBlackFast_sound sbCell1361
  · exact checkSingleBlackFast_sound sbCell1362
  · exact checkSingleBlackFast_sound sbCell1363
  · exact checkSingleBlackFast_sound sbCell1364
  · exact checkSingleBlackFast_sound sbCell1365
  · exact checkSingleBlackFast2_sound sbCell1366
  · exact checkSingleBlackFast_sound sbCell1367
  · exact checkSingleBlackFast2_sound sbCell1368

end LangtonsAnt
