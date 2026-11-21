import FastCell2
import SingleBlackEarly.C1480
import SingleBlackEarly.C1481
import SingleBlackEarly.C1482
import SingleBlackEarly.C1483
import SingleBlackEarly.C1484
import SingleBlackEarly.C1485
import SingleBlackEarly.C1486
import SingleBlackEarly.C1487
import SingleBlackEarly.C1488
import SingleBlackEarly.C1489
import SingleBlackEarly.C1490
import SingleBlackEarly.C1491
import SingleBlackEarly.C1492
import SingleBlackEarly.C1493
import SingleBlackEarly.C1494
import SingleBlackEarly.C1495
import SingleBlackEarly.C1496
import SingleBlackEarly.C1497
import SingleBlackEarly.C1498
import SingleBlackEarly.C1499
import SingleBlackEarly.C1500
import SingleBlackEarly.C1501
import SingleBlackEarly.C1502
import SingleBlackEarly.C1503
import SingleBlackEarly.C1504
import SingleBlackEarly.C1505
import SingleBlackEarly.C1506
import SingleBlackEarly.C1507
import SingleBlackEarly.C1508
import SingleBlackEarly.C1509
import SingleBlackEarly.C1510
import SingleBlackEarly.C1511
import SingleBlackEarly.C1512
import SingleBlackEarly.C1513
import SingleBlackEarly.C1514
import SingleBlackEarly.C1515
import SingleBlackEarly.C1516

namespace LangtonsAnt

def sbGroup40 : List Point :=
  [(-26, -5), (-24, -5), (-24, -6), (-25, -6), (-24, -4), (-23, -5), (-27, -1), (-28, -1), (-28, 0), (-28, -2), (-29, -2), (-29, -1), (-27, -2), (-28, -3), (-27, -5), (-28, -5), (-28, -4), (-28, -6), (-29, -6), (-29, -5), (-27, -6), (-27, -7), (-28, -7), (-26, -7), (-26, -8), (-27, -8), (-26, -6), (-25, -7), (-29, -3), (-30, -3), (-30, -2), (-30, -4), (-31, -4), (-31, -3), (-29, -4), (-30, -5), (-29, -7)]

theorem sbGroup40_ok : forall q, q ∈ sbGroup40 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup40, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell1480
  · exact checkSingleBlackFast_sound sbCell1481
  · exact checkSingleBlackFast_sound sbCell1482
  · exact checkSingleBlackFast_sound sbCell1483
  · exact checkSingleBlackFast_sound sbCell1484
  · exact checkSingleBlackFast_sound sbCell1485
  · exact checkSingleBlackFast2_sound sbCell1486
  · exact checkSingleBlackFast_sound sbCell1487
  · exact checkSingleBlackFast2_sound sbCell1488
  · exact checkSingleBlackFast_sound sbCell1489
  · exact checkSingleBlackFast_sound sbCell1490
  · exact checkSingleBlackFast2_sound sbCell1491
  · exact checkSingleBlackFast_sound sbCell1492
  · exact checkSingleBlackFast_sound sbCell1493
  · exact checkSingleBlackFast2_sound sbCell1494
  · exact checkSingleBlackFast_sound sbCell1495
  · exact checkSingleBlackFast2_sound sbCell1496
  · exact checkSingleBlackFast_sound sbCell1497
  · exact checkSingleBlackFast_sound sbCell1498
  · exact checkSingleBlackFast_sound sbCell1499
  · exact checkSingleBlack_sound sbCell1500
  · exact checkSingleBlack_sound sbCell1501
  · exact checkSingleBlackFast_sound sbCell1502
  · exact checkSingleBlackFast_sound sbCell1503
  · exact checkSingleBlackFast_sound sbCell1504
  · exact checkSingleBlackFast_sound sbCell1505
  · exact checkSingleBlackFast_sound sbCell1506
  · exact checkSingleBlackFast_sound sbCell1507
  · exact checkSingleBlackFast2_sound sbCell1508
  · exact checkSingleBlackFast_sound sbCell1509
  · exact checkSingleBlackFast_sound sbCell1510
  · exact checkSingleBlackFast_sound sbCell1511
  · exact checkSingleBlackFast2_sound sbCell1512
  · exact checkSingleBlackFast_sound sbCell1513
  · exact checkSingleBlackFast_sound sbCell1514
  · exact checkSingleBlack_sound sbCell1515
  · exact checkSingleBlackFast_sound sbCell1516

end LangtonsAnt
