import FastCell2
import SingleBlackEarly.C1443
import SingleBlackEarly.C1444
import SingleBlackEarly.C1445
import SingleBlackEarly.C1446
import SingleBlackEarly.C1447
import SingleBlackEarly.C1448
import SingleBlackEarly.C1449
import SingleBlackEarly.C1450
import SingleBlackEarly.C1451
import SingleBlackEarly.C1452
import SingleBlackEarly.C1453
import SingleBlackEarly.C1454
import SingleBlackEarly.C1455
import SingleBlackEarly.C1456
import SingleBlackEarly.C1457
import SingleBlackEarly.C1458
import SingleBlackEarly.C1459
import SingleBlackEarly.C1460
import SingleBlackEarly.C1461
import SingleBlackEarly.C1462
import SingleBlackEarly.C1463
import SingleBlackEarly.C1464
import SingleBlackEarly.C1465
import SingleBlackEarly.C1466
import SingleBlackEarly.C1467
import SingleBlackEarly.C1468
import SingleBlackEarly.C1469
import SingleBlackEarly.C1470
import SingleBlackEarly.C1471
import SingleBlackEarly.C1472
import SingleBlackEarly.C1473
import SingleBlackEarly.C1474
import SingleBlackEarly.C1475
import SingleBlackEarly.C1476
import SingleBlackEarly.C1477
import SingleBlackEarly.C1478
import SingleBlackEarly.C1479

namespace LangtonsAnt

def sbGroup39 : List Point :=
  [(-24, 3), (-24, 4), (-24, 2), (-25, 2), (-25, 3), (-23, 2), (-24, 1), (-23, -1), (-24, -1), (-24, 0), (-24, -2), (-25, -2), (-25, -1), (-23, -2), (-23, -3), (-24, -3), (-22, -3), (-22, -4), (-23, -4), (-22, -2), (-21, -3), (-25, 1), (-26, 1), (-26, 2), (-26, 0), (-27, 0), (-27, 1), (-25, 0), (-26, -1), (-25, -3), (-26, -3), (-26, -2), (-26, -4), (-27, -4), (-27, -3), (-25, -4), (-25, -5)]

theorem sbGroup39_ok : forall q, q ∈ sbGroup39 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup39, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1443
  · exact checkSingleBlackFast_sound sbCell1444
  · exact checkSingleBlackFast_sound sbCell1445
  · exact checkSingleBlackFast_sound sbCell1446
  · exact checkSingleBlackFast_sound sbCell1447
  · exact checkSingleBlackFast_sound sbCell1448
  · exact checkSingleBlackFast_sound sbCell1449
  · exact checkSingleBlackFast_sound sbCell1450
  · exact checkSingleBlackFast2_sound sbCell1451
  · exact checkSingleBlack_sound sbCell1452
  · exact checkSingleBlackFast2_sound sbCell1453
  · exact checkSingleBlack_sound sbCell1454
  · exact checkSingleBlackFast_sound sbCell1455
  · exact checkSingleBlackFast_sound sbCell1456
  · exact checkSingleBlackFast_sound sbCell1457
  · exact checkSingleBlackFast_sound sbCell1458
  · exact checkSingleBlackFast_sound sbCell1459
  · exact checkSingleBlackFast2_sound sbCell1460
  · exact checkSingleBlackFast_sound sbCell1461
  · exact checkSingleBlack_sound sbCell1462
  · exact checkSingleBlackFast_sound sbCell1463
  · exact checkSingleBlackFast2_sound sbCell1464
  · exact checkSingleBlackFast_sound sbCell1465
  · exact checkSingleBlackFast_sound sbCell1466
  · exact checkSingleBlackFast_sound sbCell1467
  · exact checkSingleBlackFast2_sound sbCell1468
  · exact checkSingleBlackFast_sound sbCell1469
  · exact checkSingleBlack_sound sbCell1470
  · exact checkSingleBlackFast_sound sbCell1471
  · exact checkSingleBlackFast2_sound sbCell1472
  · exact checkSingleBlackFast_sound sbCell1473
  · exact checkSingleBlackFast_sound sbCell1474
  · exact checkSingleBlackFast_sound sbCell1475
  · exact checkSingleBlackFast_sound sbCell1476
  · exact checkSingleBlackFast_sound sbCell1477
  · exact checkSingleBlackFast_sound sbCell1478
  · exact checkSingleBlackFast2_sound sbCell1479

end LangtonsAnt
