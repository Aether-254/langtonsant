import FastCell2
import SegmentCheck
import SingleBlackEarly.C0481
import SingleBlackEarly.C0482
import SingleBlackEarly.C0483
import SingleBlackEarly.C0484
import SingleBlackEarly.C0485
import SingleBlackEarly.C0486
import SingleBlackEarly.C0487
import SingleBlackEarly.C0488
import SingleBlackEarly.C0489
import SingleBlackEarly.C0490
import SingleBlackEarly.C0491
import SingleBlackEarly.C0492
import SingleBlackEarly.C0493
import SingleBlackEarly.C0494
import SingleBlackEarly.C0495
import SingleBlackEarly.C0496
import SingleBlackEarly.C0497
import SingleBlackEarly.C0498
import SingleBlackEarly.C0499
import SingleBlackEarly.C0500
import SingleBlackEarly.C0501
import SingleBlackEarly.C0502
import SingleBlackEarly.C0503
import SingleBlackEarly.C0504
import SingleBlackEarly.C0505
import SingleBlackEarly.C0506
import SingleBlackEarly.C0507
import SingleBlackEarly.C0508
import SingleBlackEarly.C0509
import SingleBlackEarly.C0510
import SingleBlackEarly.C0511
import SingleBlackEarly.C0512
import SingleBlackEarly.C0513
import SingleBlackEarly.C0514
import SingleBlackEarly.C0515
import SingleBlackEarly.C0516
import SingleBlackEarly.C0517

namespace LangtonsAnt

def sbGroup13 : List Point :=
  [(10, 15), (8, 14), (7, 14), (7, 15), (8, 15), (6, 14), (5, 14), (5, 15), (6, 15), (4, 14), (3, 15), (4, 15), (1, 14), (1, 15), (2, 15), (0, 15), (0, 16), (1, 16), (0, 14), (-1, 14), (-1, 15), (-1, 13), (-5, 1), (-6, 1), (-6, 2), (-6, 0), (-7, 0), (-7, 1), (-5, 0), (-6, -3), (-6, -2), (-5, -5), (-6, -5), (-6, -4), (-6, -6), (-7, -6), (-7, -5)]

theorem sbGroup13_ok : forall q, q ∈ sbGroup13 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup13, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0481
  · exact checkSingleBlackFast2_sound sbCell0482
  · exact checkSingleBlackFast_sound sbCell0483
  · exact checkSingleBlackFast_sound sbCell0484
  · exact checkSingleBlackFast_sound sbCell0485
  · exact checkSingleBlackFast2_sound sbCell0486
  · exact checkSingleBlackFast_sound sbCell0487
  · exact checkSingleBlackFast_sound sbCell0488
  · exact sbCell0489
  · exact checkSingleBlackFast_sound sbCell0490
  · exact checkSingleBlackFast2_sound sbCell0491
  · exact checkSingleBlackFast_sound sbCell0492
  · exact checkSingleBlackFast2_sound sbCell0493
  · exact checkSingleBlackFast_sound sbCell0494
  · exact checkSingleBlackFast_sound sbCell0495
  · exact checkSingleBlackFast_sound sbCell0496
  · exact checkSingleBlackFast_sound sbCell0497
  · exact checkSingleBlackFast2_sound sbCell0498
  · exact checkSingleBlackFast_sound sbCell0499
  · exact checkSingleBlackFast2_sound sbCell0500
  · exact checkSingleBlackFast_sound sbCell0501
  · exact checkSingleBlackFast_sound sbCell0502
  · exact checkSingleBlackFast_sound sbCell0503
  · exact checkSingleBlackFast_sound sbCell0504
  · exact checkSingleBlackFast_sound sbCell0505
  · exact checkSingleBlack_sound sbCell0506
  · exact checkSingleBlackFast_sound sbCell0507
  · exact checkSingleBlackFast_sound sbCell0508
  · exact checkSingleBlackFast2_sound sbCell0509
  · exact checkSingleBlackFast_sound sbCell0510
  · exact checkSingleBlackFast_sound sbCell0511
  · exact checkSingleBlackFast2_sound sbCell0512
  · exact checkSingleBlackFast_sound sbCell0513
  · exact checkSingleBlackFast_sound sbCell0514
  · exact checkSingleBlackFast_sound sbCell0515
  · exact checkSingleBlackFast2_sound sbCell0516
  · exact checkSingleBlackFast_sound sbCell0517

end LangtonsAnt
