import FastCell2
import SegmentCheck
import SingleBlackEarly.C1554
import SingleBlackEarly.C1555
import SingleBlackEarly.C1556
import SingleBlackEarly.C1557
import SingleBlackEarly.C1558
import SingleBlackEarly.C1559
import SingleBlackEarly.C1560
import SingleBlackEarly.C1561
import SingleBlackEarly.C1562
import SingleBlackEarly.C1563
import SingleBlackEarly.C1564
import SingleBlackEarly.C1565
import SingleBlackEarly.C1566
import SingleBlackEarly.C1567
import SingleBlackEarly.C1568
import SingleBlackEarly.C1569
import SingleBlackEarly.C1570
import SingleBlackEarly.C1571
import SingleBlackEarly.C1572
import SingleBlackEarly.C1573
import SingleBlackEarly.C1574
import SingleBlackEarly.C1575
import SingleBlackEarly.C1576
import SingleBlackEarly.C1577
import SingleBlackEarly.C1578
import SingleBlackEarly.C1579
import SingleBlackEarly.C1580
import SingleBlackEarly.C1581
import SingleBlackEarly.C1582
import SingleBlackEarly.C1583
import SingleBlackEarly.C1584
import SingleBlackEarly.C1585
import SingleBlackEarly.C1586
import SingleBlackEarly.C1587
import SingleBlackEarly.C1588
import SingleBlackEarly.C1589
import SingleBlackEarly.C1590

namespace LangtonsAnt

def sbGroup42 : List Point :=
  [(-34, -6), (-34, -8), (-35, -8), (-35, -7), (-33, -8), (-34, -9), (-33, -11), (-34, -11), (-34, -10), (-34, -12), (-35, -12), (-35, -11), (-33, -12), (-33, -13), (-34, -13), (-32, -13), (-32, -14), (-33, -14), (-32, -12), (-31, -13), (-35, -9), (-36, -9), (-36, -8), (-36, -10), (-37, -10), (-37, -9), (-35, -10), (-36, -11), (-35, -13), (-36, -13), (-36, -12), (-36, -14), (-37, -14), (-37, -13), (-35, -14), (-35, -15), (-36, -15)]

theorem sbGroup42_ok : forall q, q ∈ sbGroup42 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup42, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlack_sound sbCell1554
  · exact checkSingleBlackFast_sound sbCell1555
  · exact checkSingleBlackFast_sound sbCell1556
  · exact checkSingleBlackFast_sound sbCell1557
  · exact checkSingleBlackFast_sound sbCell1558
  · exact checkSingleBlackFast_sound sbCell1559
  · exact checkSingleBlackFast_sound sbCell1560
  · exact checkSingleBlackFast_sound sbCell1561
  · exact checkSingleBlack_sound sbCell1562
  · exact checkSingleBlackFast_sound sbCell1563
  · exact checkSingleBlackFast2_sound sbCell1564
  · exact checkSingleBlackFast_sound sbCell1565
  · exact checkSingleBlackFast_sound sbCell1566
  · exact checkSingleBlackFast_sound sbCell1567
  · exact checkSingleBlackFast2_sound sbCell1568
  · exact checkSingleBlackFast_sound sbCell1569
  · exact checkSingleBlack_sound sbCell1570
  · exact checkSingleBlackFast2_sound sbCell1571
  · exact checkSingleBlackFast_sound sbCell1572
  · exact checkSingleBlackFast_sound sbCell1573
  · exact checkSingleBlackFast2_sound sbCell1574
  · exact checkSingleBlackFast_sound sbCell1575
  · exact checkSingleBlackFast2_sound sbCell1576
  · exact checkSingleBlackFast_sound sbCell1577
  · exact checkSingleBlackFast_sound sbCell1578
  · exact checkSingleBlackFast_sound sbCell1579
  · exact checkSingleBlackFast_sound sbCell1580
  · exact sbCell1581
  · exact checkSingleBlackFast_sound sbCell1582
  · exact checkSingleBlackFast_sound sbCell1583
  · exact checkSingleBlack_sound sbCell1584
  · exact checkSingleBlackFast_sound sbCell1585
  · exact checkSingleBlackFast2_sound sbCell1586
  · exact checkSingleBlackFast2_sound sbCell1587
  · exact checkSingleBlackFast_sound sbCell1588
  · exact checkSingleBlackFast_sound sbCell1589
  · exact checkSingleBlackFast2_sound sbCell1590

end LangtonsAnt
