import FastCell2
import SingleBlackEarly.C1406
import SingleBlackEarly.C1407
import SingleBlackEarly.C1408
import SingleBlackEarly.C1409
import SingleBlackEarly.C1410
import SingleBlackEarly.C1411
import SingleBlackEarly.C1412
import SingleBlackEarly.C1413
import SingleBlackEarly.C1414
import SingleBlackEarly.C1415
import SingleBlackEarly.C1416
import SingleBlackEarly.C1417
import SingleBlackEarly.C1418
import SingleBlackEarly.C1419
import SingleBlackEarly.C1420
import SingleBlackEarly.C1421
import SingleBlackEarly.C1422
import SingleBlackEarly.C1423
import SingleBlackEarly.C1424
import SingleBlackEarly.C1425
import SingleBlackEarly.C1426
import SingleBlackEarly.C1427
import SingleBlackEarly.C1428
import SingleBlackEarly.C1429
import SingleBlackEarly.C1430
import SingleBlackEarly.C1431
import SingleBlackEarly.C1432
import SingleBlackEarly.C1433
import SingleBlackEarly.C1434
import SingleBlackEarly.C1435
import SingleBlackEarly.C1436
import SingleBlackEarly.C1437
import SingleBlackEarly.C1438
import SingleBlackEarly.C1439
import SingleBlackEarly.C1440
import SingleBlackEarly.C1441
import SingleBlackEarly.C1442

namespace LangtonsAnt

def sbGroup38 : List Point :=
  [(-19, 3), (-20, 3), (-20, 4), (-20, 2), (-21, 2), (-21, 3), (-19, 2), (-19, 1), (-20, 1), (-18, 1), (-18, 0), (-19, 0), (-18, 2), (-17, 1), (-21, 5), (-22, 5), (-22, 6), (-22, 4), (-23, 4), (-23, 5), (-21, 4), (-22, 3), (-21, 1), (-22, 1), (-22, 2), (-22, 0), (-23, 0), (-23, 1), (-21, 0), (-21, -1), (-22, -1), (-20, -1), (-20, -2), (-21, -2), (-20, 0), (-19, -1), (-23, 3)]

theorem sbGroup38_ok : forall q, q ∈ sbGroup38 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup38, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1406
  · exact checkSingleBlackFast2_sound sbCell1407
  · exact checkSingleBlackFast2_sound sbCell1408
  · exact checkSingleBlackFast_sound sbCell1409
  · exact checkSingleBlackFast2_sound sbCell1410
  · exact checkSingleBlackFast2_sound sbCell1411
  · exact checkSingleBlackFast2_sound sbCell1412
  · exact checkSingleBlackFast2_sound sbCell1413
  · exact checkSingleBlackFast_sound sbCell1414
  · exact checkSingleBlackFast2_sound sbCell1415
  · exact checkSingleBlackFast2_sound sbCell1416
  · exact checkSingleBlackFast2_sound sbCell1417
  · exact checkSingleBlackFast_sound sbCell1418
  · exact checkSingleBlackFast_sound sbCell1419
  · exact checkSingleBlackFast2_sound sbCell1420
  · exact checkSingleBlackFast2_sound sbCell1421
  · exact checkSingleBlackFast2_sound sbCell1422
  · exact checkSingleBlackFast_sound sbCell1423
  · exact checkSingleBlackFast_sound sbCell1424
  · exact checkSingleBlackFast2_sound sbCell1425
  · exact checkSingleBlackFast_sound sbCell1426
  · exact checkSingleBlackFast_sound sbCell1427
  · exact checkSingleBlackFast2_sound sbCell1428
  · exact checkSingleBlackFast_sound sbCell1429
  · exact checkSingleBlackFast_sound sbCell1430
  · exact checkSingleBlackFast_sound sbCell1431
  · exact checkSingleBlackFast_sound sbCell1432
  · exact checkSingleBlackFast_sound sbCell1433
  · exact checkSingleBlackFast_sound sbCell1434
  · exact checkSingleBlackFast_sound sbCell1435
  · exact checkSingleBlackFast_sound sbCell1436
  · exact checkSingleBlackFast_sound sbCell1437
  · exact checkSingleBlackFast2_sound sbCell1438
  · exact checkSingleBlackFast_sound sbCell1439
  · exact checkSingleBlackFast_sound sbCell1440
  · exact checkSingleBlackFast2_sound sbCell1441
  · exact checkSingleBlackFast2_sound sbCell1442

end LangtonsAnt
