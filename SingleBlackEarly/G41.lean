import FastCell2
import SegmentCheck
import SingleBlackEarly.C1517
import SingleBlackEarly.C1518
import SingleBlackEarly.C1519
import SingleBlackEarly.C1520
import SingleBlackEarly.C1521
import SingleBlackEarly.C1522
import SingleBlackEarly.C1523
import SingleBlackEarly.C1524
import SingleBlackEarly.C1525
import SingleBlackEarly.C1526
import SingleBlackEarly.C1527
import SingleBlackEarly.C1528
import SingleBlackEarly.C1529
import SingleBlackEarly.C1530
import SingleBlackEarly.C1531
import SingleBlackEarly.C1532
import SingleBlackEarly.C1533
import SingleBlackEarly.C1534
import SingleBlackEarly.C1535
import SingleBlackEarly.C1536
import SingleBlackEarly.C1537
import SingleBlackEarly.C1538
import SingleBlackEarly.C1539
import SingleBlackEarly.C1540
import SingleBlackEarly.C1541
import SingleBlackEarly.C1542
import SingleBlackEarly.C1543
import SingleBlackEarly.C1544
import SingleBlackEarly.C1545
import SingleBlackEarly.C1546
import SingleBlackEarly.C1547
import SingleBlackEarly.C1548
import SingleBlackEarly.C1549
import SingleBlackEarly.C1550
import SingleBlackEarly.C1551
import SingleBlackEarly.C1552
import SingleBlackEarly.C1553

namespace LangtonsAnt

def sbGroup41 : List Point :=
  [(-30, -7), (-30, -6), (-30, -8), (-31, -8), (-31, -7), (-29, -8), (-29, -9), (-30, -9), (-28, -9), (-28, -10), (-29, -10), (-28, -8), (-27, -9), (-31, -5), (-32, -5), (-32, -4), (-32, -6), (-33, -6), (-33, -5), (-31, -6), (-32, -7), (-31, -9), (-32, -9), (-32, -8), (-32, -10), (-33, -10), (-33, -9), (-31, -10), (-31, -11), (-32, -11), (-30, -11), (-30, -12), (-31, -12), (-30, -10), (-29, -11), (-33, -7), (-34, -7)]

theorem sbGroup41_ok : forall q, q ∈ sbGroup41 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup41, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1517
  · exact checkSingleBlackFast2_sound sbCell1518
  · exact checkSingleBlackFast_sound sbCell1519
  · exact checkSingleBlackFast_sound sbCell1520
  · exact checkSingleBlackFast_sound sbCell1521
  · exact checkSingleBlackFast_sound sbCell1522
  · exact sbCell1523
  · exact checkSingleBlackFast_sound sbCell1524
  · exact checkSingleBlackFast_sound sbCell1525
  · exact checkSingleBlack_sound sbCell1526
  · exact checkSingleBlackFast2_sound sbCell1527
  · exact checkSingleBlackFast_sound sbCell1528
  · exact checkSingleBlackFast_sound sbCell1529
  · exact checkSingleBlackFast2_sound sbCell1530
  · exact checkSingleBlackFast_sound sbCell1531
  · exact checkSingleBlackFast2_sound sbCell1532
  · exact checkSingleBlackFast_sound sbCell1533
  · exact checkSingleBlack_sound sbCell1534
  · exact checkSingleBlackFast_sound sbCell1535
  · exact checkSingleBlackFast_sound sbCell1536
  · exact checkSingleBlackFast_sound sbCell1537
  · exact checkSingleBlackFast_sound sbCell1538
  · exact checkSingleBlackFast_sound sbCell1539
  · exact checkSingleBlackFast2_sound sbCell1540
  · exact checkSingleBlackFast_sound sbCell1541
  · exact checkSingleBlackFast_sound sbCell1542
  · exact checkSingleBlackFast_sound sbCell1543
  · exact checkSingleBlackFast_sound sbCell1544
  · exact checkSingleBlackFast_sound sbCell1545
  · exact checkSingleBlackFast_sound sbCell1546
  · exact checkSingleBlackFast2_sound sbCell1547
  · exact checkSingleBlackFast_sound sbCell1548
  · exact checkSingleBlackFast_sound sbCell1549
  · exact checkSingleBlackFast_sound sbCell1550
  · exact checkSingleBlackFast_sound sbCell1551
  · exact checkSingleBlackFast2_sound sbCell1552
  · exact checkSingleBlackFast_sound sbCell1553

end LangtonsAnt
