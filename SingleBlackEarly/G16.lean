import FastCell2
import SingleBlackEarly.C0592
import SingleBlackEarly.C0593
import SingleBlackEarly.C0594
import SingleBlackEarly.C0595
import SingleBlackEarly.C0596
import SingleBlackEarly.C0597
import SingleBlackEarly.C0598
import SingleBlackEarly.C0599
import SingleBlackEarly.C0600
import SingleBlackEarly.C0601
import SingleBlackEarly.C0602
import SingleBlackEarly.C0603
import SingleBlackEarly.C0604
import SingleBlackEarly.C0605
import SingleBlackEarly.C0606
import SingleBlackEarly.C0607
import SingleBlackEarly.C0608
import SingleBlackEarly.C0609
import SingleBlackEarly.C0610
import SingleBlackEarly.C0611
import SingleBlackEarly.C0612
import SingleBlackEarly.C0613
import SingleBlackEarly.C0614
import SingleBlackEarly.C0615
import SingleBlackEarly.C0616
import SingleBlackEarly.C0617
import SingleBlackEarly.C0618
import SingleBlackEarly.C0619
import SingleBlackEarly.C0620
import SingleBlackEarly.C0621
import SingleBlackEarly.C0622
import SingleBlackEarly.C0623
import SingleBlackEarly.C0624
import SingleBlackEarly.C0625
import SingleBlackEarly.C0626
import SingleBlackEarly.C0627
import SingleBlackEarly.C0628

namespace LangtonsAnt

def sbGroup16 : List Point :=
  [(20, 12), (20, 14), (21, 14), (21, 13), (19, 14), (19, 15), (20, 15), (18, 15), (18, 16), (19, 16), (18, 14), (15, 13), (15, 14), (15, 15), (16, 15), (14, 15), (14, 16), (15, 16), (14, 14), (3, -7), (6, -6), (5, -6), (4, -7), (4, -8), (3, -8), (5, -8), (5, -9), (4, -9), (5, -7), (6, -7), (6, -8), (7, -8), (7, -9), (6, -9), (7, -7), (8, -7), (8, -8)]

theorem sbGroup16_ok : forall q, q ∈ sbGroup16 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup16, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0592
  · exact checkSingleBlackFast_sound sbCell0593
  · exact checkSingleBlackFast_sound sbCell0594
  · exact checkSingleBlackFast_sound sbCell0595
  · exact checkSingleBlackFast2_sound sbCell0596
  · exact checkSingleBlackFast_sound sbCell0597
  · exact checkSingleBlackFast_sound sbCell0598
  · exact checkSingleBlackFast_sound sbCell0599
  · exact checkSingleBlackFast_sound sbCell0600
  · exact checkSingleBlackFast_sound sbCell0601
  · exact checkSingleBlackFast_sound sbCell0602
  · exact checkSingleBlackFast2_sound sbCell0603
  · exact checkSingleBlackFast2_sound sbCell0604
  · exact checkSingleBlackFast_sound sbCell0605
  · exact checkSingleBlack_sound sbCell0606
  · exact checkSingleBlackFast_sound sbCell0607
  · exact checkSingleBlackFast_sound sbCell0608
  · exact checkSingleBlackFast_sound sbCell0609
  · exact checkSingleBlackFast_sound sbCell0610
  · exact checkSingleBlackFast_sound sbCell0611
  · exact checkSingleBlackFast_sound sbCell0612
  · exact checkSingleBlackFast_sound sbCell0613
  · exact checkSingleBlackFast_sound sbCell0614
  · exact checkSingleBlackFast_sound sbCell0615
  · exact checkSingleBlackFast2_sound sbCell0616
  · exact checkSingleBlackFast_sound sbCell0617
  · exact checkSingleBlackFast_sound sbCell0618
  · exact checkSingleBlackFast2_sound sbCell0619
  · exact checkSingleBlackFast2_sound sbCell0620
  · exact checkSingleBlackFast_sound sbCell0621
  · exact checkSingleBlackFast_sound sbCell0622
  · exact checkSingleBlackFast_sound sbCell0623
  · exact checkSingleBlackFast2_sound sbCell0624
  · exact checkSingleBlackFast_sound sbCell0625
  · exact checkSingleBlackFast_sound sbCell0626
  · exact checkSingleBlackFast_sound sbCell0627
  · exact checkSingleBlackFast_sound sbCell0628

end LangtonsAnt
