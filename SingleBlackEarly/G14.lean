import FastCell2
import SegmentCheck
import SingleBlackEarly.C0518
import SingleBlackEarly.C0519
import SingleBlackEarly.C0520
import SingleBlackEarly.C0521
import SingleBlackEarly.C0522
import SingleBlackEarly.C0523
import SingleBlackEarly.C0524
import SingleBlackEarly.C0525
import SingleBlackEarly.C0526
import SingleBlackEarly.C0527
import SingleBlackEarly.C0528
import SingleBlackEarly.C0529
import SingleBlackEarly.C0530
import SingleBlackEarly.C0531
import SingleBlackEarly.C0532
import SingleBlackEarly.C0533
import SingleBlackEarly.C0534
import SingleBlackEarly.C0535
import SingleBlackEarly.C0536
import SingleBlackEarly.C0537
import SingleBlackEarly.C0538
import SingleBlackEarly.C0539
import SingleBlackEarly.C0540
import SingleBlackEarly.C0541
import SingleBlackEarly.C0542
import SingleBlackEarly.C0543
import SingleBlackEarly.C0544
import SingleBlackEarly.C0545
import SingleBlackEarly.C0546
import SingleBlackEarly.C0547
import SingleBlackEarly.C0548
import SingleBlackEarly.C0549
import SingleBlackEarly.C0550
import SingleBlackEarly.C0551
import SingleBlackEarly.C0552
import SingleBlackEarly.C0553
import SingleBlackEarly.C0554

namespace LangtonsAnt

def sbGroup14 : List Point :=
  [(-5, -6), (-5, -7), (-6, -7), (-4, -7), (-4, -8), (-5, -8), (-4, -6), (0, -5), (0, -6), (-1, -6), (1, -6), (1, -7), (0, -7), (1, -5), (2, -7), (2, -8), (1, -8), (2, -6), (-1, -7), (-2, -7), (7, -3), (7, -4), (7, -5), (6, -5), (8, -5), (8, -6), (7, -6), (8, -4), (9, -4), (9, -5), (10, -6), (9, -6), (10, -3), (17, -6), (17, -7), (16, -7), (18, -7)]

theorem sbGroup14_ok : forall q, q ∈ sbGroup14 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup14, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast2_sound sbCell0518
  · exact checkSingleBlackFast_sound sbCell0519
  · exact checkSingleBlackFast_sound sbCell0520
  · exact checkSingleBlackFast_sound sbCell0521
  · exact checkSingleBlackFast_sound sbCell0522
  · exact checkSingleBlackFast_sound sbCell0523
  · exact checkSingleBlackFast_sound sbCell0524
  · exact checkSingleBlackFast_sound sbCell0525
  · exact checkSingleBlack_sound sbCell0526
  · exact checkSingleBlackFast2_sound sbCell0527
  · exact checkSingleBlackFast2_sound sbCell0528
  · exact checkSingleBlackFast_sound sbCell0529
  · exact checkSingleBlackFast_sound sbCell0530
  · exact checkSingleBlackFast_sound sbCell0531
  · exact checkSingleBlackFast2_sound sbCell0532
  · exact checkSingleBlackFast_sound sbCell0533
  · exact checkSingleBlackFast_sound sbCell0534
  · exact checkSingleBlackFast2_sound sbCell0535
  · exact checkSingleBlack_sound sbCell0536
  · exact checkSingleBlackFast_sound sbCell0537
  · exact checkSingleBlackFast2_sound sbCell0538
  · exact checkSingleBlackFast_sound sbCell0539
  · exact checkSingleBlackFast_sound sbCell0540
  · exact checkSingleBlackFast_sound sbCell0541
  · exact checkSingleBlackFast2_sound sbCell0542
  · exact checkSingleBlackFast_sound sbCell0543
  · exact checkSingleBlackFast_sound sbCell0544
  · exact checkSingleBlackFast_sound sbCell0545
  · exact checkSingleBlackFast2_sound sbCell0546
  · exact checkSingleBlackFast_sound sbCell0547
  · exact checkSingleBlackFast2_sound sbCell0548
  · exact checkSingleBlackFast_sound sbCell0549
  · exact checkSingleBlackFast_sound sbCell0550
  · exact sbCell0551
  · exact checkSingleBlackFast2_sound sbCell0552
  · exact checkSingleBlackFast2_sound sbCell0553
  · exact checkSingleBlackFast_sound sbCell0554

end LangtonsAnt
