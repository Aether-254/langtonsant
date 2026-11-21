import FastCell2
import SingleBlackEarly.C1369
import SingleBlackEarly.C1370
import SingleBlackEarly.C1371
import SingleBlackEarly.C1372
import SingleBlackEarly.C1373
import SingleBlackEarly.C1374
import SingleBlackEarly.C1375
import SingleBlackEarly.C1376
import SingleBlackEarly.C1377
import SingleBlackEarly.C1378
import SingleBlackEarly.C1379
import SingleBlackEarly.C1380
import SingleBlackEarly.C1381
import SingleBlackEarly.C1382
import SingleBlackEarly.C1383
import SingleBlackEarly.C1384
import SingleBlackEarly.C1385
import SingleBlackEarly.C1386
import SingleBlackEarly.C1387
import SingleBlackEarly.C1388
import SingleBlackEarly.C1389
import SingleBlackEarly.C1390
import SingleBlackEarly.C1391
import SingleBlackEarly.C1392
import SingleBlackEarly.C1393
import SingleBlackEarly.C1394
import SingleBlackEarly.C1395
import SingleBlackEarly.C1396
import SingleBlackEarly.C1397
import SingleBlackEarly.C1398
import SingleBlackEarly.C1399
import SingleBlackEarly.C1400
import SingleBlackEarly.C1401
import SingleBlackEarly.C1402
import SingleBlackEarly.C1403
import SingleBlackEarly.C1404
import SingleBlackEarly.C1405

namespace LangtonsAnt

def sbGroup37 : List Point :=
  [(-18, 13), (-18, 14), (-18, 12), (-19, 12), (-19, 13), (-17, 12), (-16, 9), (-17, 9), (-18, 9), (-18, 10), (-18, 8), (-19, 8), (-19, 9), (-17, 8), (-18, 7), (-17, 5), (-18, 5), (-18, 6), (-18, 4), (-19, 4), (-19, 5), (-17, 4), (-17, 3), (-18, 3), (-16, 3), (-16, 2), (-17, 2), (-16, 4), (-15, 3), (-19, 7), (-20, 7), (-20, 8), (-20, 6), (-21, 6), (-21, 7), (-19, 6), (-20, 5)]

theorem sbGroup37_ok : forall q, q ∈ sbGroup37 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup37, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1369
  · exact checkSingleBlackFast2_sound sbCell1370
  · exact checkSingleBlackFast_sound sbCell1371
  · exact checkSingleBlackFast2_sound sbCell1372
  · exact checkSingleBlackFast_sound sbCell1373
  · exact checkSingleBlackFast2_sound sbCell1374
  · exact checkSingleBlackFast_sound sbCell1375
  · exact checkSingleBlackFast_sound sbCell1376
  · exact checkSingleBlackFast_sound sbCell1377
  · exact checkSingleBlackFast2_sound sbCell1378
  · exact checkSingleBlackFast_sound sbCell1379
  · exact checkSingleBlackFast2_sound sbCell1380
  · exact checkSingleBlackFast_sound sbCell1381
  · exact checkSingleBlackFast2_sound sbCell1382
  · exact checkSingleBlackFast2_sound sbCell1383
  · exact checkSingleBlackFast2_sound sbCell1384
  · exact checkSingleBlackFast2_sound sbCell1385
  · exact checkSingleBlackFast2_sound sbCell1386
  · exact checkSingleBlackFast_sound sbCell1387
  · exact checkSingleBlackFast_sound sbCell1388
  · exact checkSingleBlackFast2_sound sbCell1389
  · exact checkSingleBlackFast_sound sbCell1390
  · exact checkSingleBlackFast_sound sbCell1391
  · exact checkSingleBlackFast2_sound sbCell1392
  · exact checkSingleBlackFast2_sound sbCell1393
  · exact checkSingleBlack_sound sbCell1394
  · exact checkSingleBlackFast2_sound sbCell1395
  · exact checkSingleBlackFast2_sound sbCell1396
  · exact checkSingleBlackFast_sound sbCell1397
  · exact checkSingleBlackFast2_sound sbCell1398
  · exact checkSingleBlackFast_sound sbCell1399
  · exact checkSingleBlackFast2_sound sbCell1400
  · exact checkSingleBlackFast2_sound sbCell1401
  · exact checkSingleBlackFast2_sound sbCell1402
  · exact checkSingleBlackFast_sound sbCell1403
  · exact checkSingleBlackFast2_sound sbCell1404
  · exact checkSingleBlackFast2_sound sbCell1405

end LangtonsAnt
