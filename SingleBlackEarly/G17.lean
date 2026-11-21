import FastCell2
import SingleBlackEarly.C0629
import SingleBlackEarly.C0630
import SingleBlackEarly.C0631
import SingleBlackEarly.C0632
import SingleBlackEarly.C0633
import SingleBlackEarly.C0634
import SingleBlackEarly.C0635
import SingleBlackEarly.C0636
import SingleBlackEarly.C0637
import SingleBlackEarly.C0638
import SingleBlackEarly.C0639
import SingleBlackEarly.C0640
import SingleBlackEarly.C0641
import SingleBlackEarly.C0642
import SingleBlackEarly.C0643
import SingleBlackEarly.C0644
import SingleBlackEarly.C0645
import SingleBlackEarly.C0646
import SingleBlackEarly.C0647
import SingleBlackEarly.C0648
import SingleBlackEarly.C0649
import SingleBlackEarly.C0650
import SingleBlackEarly.C0651
import SingleBlackEarly.C0652
import SingleBlackEarly.C0653
import SingleBlackEarly.C0654
import SingleBlackEarly.C0655
import SingleBlackEarly.C0656
import SingleBlackEarly.C0657
import SingleBlackEarly.C0658
import SingleBlackEarly.C0659
import SingleBlackEarly.C0660
import SingleBlackEarly.C0661
import SingleBlackEarly.C0662
import SingleBlackEarly.C0663
import SingleBlackEarly.C0664
import SingleBlackEarly.C0665

namespace LangtonsAnt

def sbGroup17 : List Point :=
  [(9, -8), (9, -9), (8, -9), (9, -7), (10, -7), (10, -8), (11, -7), (14, -8), (13, -8), (11, -8), (11, -9), (10, -9), (8, -10), (7, -10), (6, -10), (5, -10), (4, -10), (3, -10), (3, -9), (9, -10), (9, -11), (8, -11), (10, -11), (10, -12), (9, -12), (10, -10), (11, -10), (11, -11), (12, -11), (12, -12), (11, -12), (12, -10), (13, -10), (13, -11), (13, -9), (14, -9), (14, -10)]

theorem sbGroup17_ok : forall q, q ∈ sbGroup17 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup17, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0629
  · exact checkSingleBlackFast_sound sbCell0630
  · exact checkSingleBlackFast_sound sbCell0631
  · exact checkSingleBlackFast_sound sbCell0632
  · exact checkSingleBlackFast_sound sbCell0633
  · exact checkSingleBlackFast_sound sbCell0634
  · exact checkSingleBlackFast2_sound sbCell0635
  · exact checkSingleBlackFast2_sound sbCell0636
  · exact checkSingleBlackFast_sound sbCell0637
  · exact checkSingleBlackFast_sound sbCell0638
  · exact checkSingleBlackFast_sound sbCell0639
  · exact checkSingleBlackFast_sound sbCell0640
  · exact checkSingleBlackFast_sound sbCell0641
  · exact checkSingleBlackFast_sound sbCell0642
  · exact checkSingleBlackFast_sound sbCell0643
  · exact checkSingleBlackFast2_sound sbCell0644
  · exact checkSingleBlackFast_sound sbCell0645
  · exact checkSingleBlackFast_sound sbCell0646
  · exact checkSingleBlackFast_sound sbCell0647
  · exact checkSingleBlackFast_sound sbCell0648
  · exact checkSingleBlackFast_sound sbCell0649
  · exact checkSingleBlackFast_sound sbCell0650
  · exact checkSingleBlackFast_sound sbCell0651
  · exact checkSingleBlackFast_sound sbCell0652
  · exact checkSingleBlackFast_sound sbCell0653
  · exact checkSingleBlackFast_sound sbCell0654
  · exact checkSingleBlackFast_sound sbCell0655
  · exact checkSingleBlackFast_sound sbCell0656
  · exact checkSingleBlackFast2_sound sbCell0657
  · exact checkSingleBlackFast2_sound sbCell0658
  · exact checkSingleBlackFast_sound sbCell0659
  · exact checkSingleBlackFast_sound sbCell0660
  · exact checkSingleBlackFast_sound sbCell0661
  · exact checkSingleBlackFast_sound sbCell0662
  · exact checkSingleBlackFast_sound sbCell0663
  · exact checkSingleBlackFast2_sound sbCell0664
  · exact checkSingleBlackFast_sound sbCell0665

end LangtonsAnt
