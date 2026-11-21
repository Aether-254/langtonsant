import FastCell2
import SingleBlackEarly.C0666
import SingleBlackEarly.C0667
import SingleBlackEarly.C0668
import SingleBlackEarly.C0669
import SingleBlackEarly.C0670
import SingleBlackEarly.C0671
import SingleBlackEarly.C0672
import SingleBlackEarly.C0673
import SingleBlackEarly.C0674
import SingleBlackEarly.C0675
import SingleBlackEarly.C0676
import SingleBlackEarly.C0677
import SingleBlackEarly.C0678
import SingleBlackEarly.C0679
import SingleBlackEarly.C0680
import SingleBlackEarly.C0681
import SingleBlackEarly.C0682
import SingleBlackEarly.C0683
import SingleBlackEarly.C0684
import SingleBlackEarly.C0685
import SingleBlackEarly.C0686
import SingleBlackEarly.C0687
import SingleBlackEarly.C0688
import SingleBlackEarly.C0689
import SingleBlackEarly.C0690
import SingleBlackEarly.C0691
import SingleBlackEarly.C0692
import SingleBlackEarly.C0693
import SingleBlackEarly.C0694
import SingleBlackEarly.C0695
import SingleBlackEarly.C0696
import SingleBlackEarly.C0697
import SingleBlackEarly.C0698
import SingleBlackEarly.C0699
import SingleBlackEarly.C0700
import SingleBlackEarly.C0701
import SingleBlackEarly.C0702

namespace LangtonsAnt

def sbGroup18 : List Point :=
  [(12, -9), (12, -8), (15, -8), (15, -9), (15, -10), (15, -11), (14, -11), (16, -11), (16, -12), (15, -12), (16, -10), (17, -10), (17, -11), (17, -9), (18, -9), (18, -10), (16, -9), (16, -8), (19, -8), (19, -9), (19, -10), (19, -11), (18, -11), (20, -11), (20, -12), (19, -12), (20, -10), (21, -10), (21, -11), (21, -9), (22, -9), (22, -10), (20, -9), (20, -8), (21, -8), (21, -7), (22, -7)]

theorem sbGroup18_ok : forall q, q ∈ sbGroup18 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup18, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0666
  · exact checkSingleBlackFast_sound sbCell0667
  · exact checkSingleBlackFast_sound sbCell0668
  · exact checkSingleBlackFast_sound sbCell0669
  · exact checkSingleBlackFast_sound sbCell0670
  · exact checkSingleBlackFast_sound sbCell0671
  · exact checkSingleBlack_sound sbCell0672
  · exact checkSingleBlackFast_sound sbCell0673
  · exact checkSingleBlack_sound sbCell0674
  · exact checkSingleBlackFast_sound sbCell0675
  · exact checkSingleBlackFast_sound sbCell0676
  · exact checkSingleBlackFast_sound sbCell0677
  · exact checkSingleBlackFast_sound sbCell0678
  · exact checkSingleBlackFast_sound sbCell0679
  · exact checkSingleBlackFast_sound sbCell0680
  · exact checkSingleBlackFast_sound sbCell0681
  · exact checkSingleBlackFast2_sound sbCell0682
  · exact checkSingleBlackFast_sound sbCell0683
  · exact checkSingleBlackFast_sound sbCell0684
  · exact checkSingleBlackFast_sound sbCell0685
  · exact checkSingleBlack_sound sbCell0686
  · exact checkSingleBlackFast_sound sbCell0687
  · exact checkSingleBlackFast2_sound sbCell0688
  · exact checkSingleBlackFast_sound sbCell0689
  · exact checkSingleBlackFast2_sound sbCell0690
  · exact checkSingleBlackFast_sound sbCell0691
  · exact checkSingleBlackFast_sound sbCell0692
  · exact checkSingleBlackFast_sound sbCell0693
  · exact checkSingleBlackFast_sound sbCell0694
  · exact checkSingleBlackFast_sound sbCell0695
  · exact checkSingleBlackFast2_sound sbCell0696
  · exact checkSingleBlackFast_sound sbCell0697
  · exact checkSingleBlackFast_sound sbCell0698
  · exact checkSingleBlackFast_sound sbCell0699
  · exact checkSingleBlackFast2_sound sbCell0700
  · exact checkSingleBlackFast_sound sbCell0701
  · exact checkSingleBlackFast_sound sbCell0702

end LangtonsAnt
