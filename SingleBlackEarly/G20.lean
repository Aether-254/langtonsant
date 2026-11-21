import FastCell2
import SingleBlackEarly.C0740
import SingleBlackEarly.C0741
import SingleBlackEarly.C0742
import SingleBlackEarly.C0743
import SingleBlackEarly.C0744
import SingleBlackEarly.C0745
import SingleBlackEarly.C0746
import SingleBlackEarly.C0747
import SingleBlackEarly.C0748
import SingleBlackEarly.C0749
import SingleBlackEarly.C0750
import SingleBlackEarly.C0751
import SingleBlackEarly.C0752
import SingleBlackEarly.C0753
import SingleBlackEarly.C0754
import SingleBlackEarly.C0755
import SingleBlackEarly.C0756
import SingleBlackEarly.C0757
import SingleBlackEarly.C0758
import SingleBlackEarly.C0759
import SingleBlackEarly.C0760
import SingleBlackEarly.C0761
import SingleBlackEarly.C0762
import SingleBlackEarly.C0763
import SingleBlackEarly.C0764
import SingleBlackEarly.C0765
import SingleBlackEarly.C0766
import SingleBlackEarly.C0767
import SingleBlackEarly.C0768
import SingleBlackEarly.C0769
import SingleBlackEarly.C0770
import SingleBlackEarly.C0771
import SingleBlackEarly.C0772
import SingleBlackEarly.C0773
import SingleBlackEarly.C0774
import SingleBlackEarly.C0775
import SingleBlackEarly.C0776

namespace LangtonsAnt

def sbGroup20 : List Point :=
  [(18, -14), (17, -14), (18, -12), (21, -12), (21, -13), (20, -13), (22, -13), (22, -14), (21, -14), (22, -12), (23, -12), (23, -13), (23, -11), (24, -11), (24, -12), (22, -11), (20, -14), (19, -14), (19, -13), (19, -15), (18, -15), (17, -15), (16, -15), (16, -14), (20, -15), (20, -16), (19, -16), (21, -16), (21, -17), (20, -17), (21, -15), (22, -15), (22, -16), (23, -16), (23, -17), (22, -17), (23, -15)]

theorem sbGroup20_ok : forall q, q ∈ sbGroup20 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup20, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0740
  · exact checkSingleBlackFast_sound sbCell0741
  · exact checkSingleBlackFast_sound sbCell0742
  · exact checkSingleBlackFast_sound sbCell0743
  · exact checkSingleBlackFast2_sound sbCell0744
  · exact checkSingleBlackFast_sound sbCell0745
  · exact checkSingleBlackFast2_sound sbCell0746
  · exact checkSingleBlackFast_sound sbCell0747
  · exact checkSingleBlackFast_sound sbCell0748
  · exact checkSingleBlackFast_sound sbCell0749
  · exact checkSingleBlackFast2_sound sbCell0750
  · exact checkSingleBlackFast_sound sbCell0751
  · exact checkSingleBlackFast_sound sbCell0752
  · exact checkSingleBlackFast2_sound sbCell0753
  · exact checkSingleBlack_sound sbCell0754
  · exact checkSingleBlackFast_sound sbCell0755
  · exact checkSingleBlackFast_sound sbCell0756
  · exact checkSingleBlackFast_sound sbCell0757
  · exact checkSingleBlackFast_sound sbCell0758
  · exact checkSingleBlackFast_sound sbCell0759
  · exact checkSingleBlackFast2_sound sbCell0760
  · exact checkSingleBlackFast_sound sbCell0761
  · exact checkSingleBlackFast_sound sbCell0762
  · exact checkSingleBlackFast_sound sbCell0763
  · exact checkSingleBlack_sound sbCell0764
  · exact checkSingleBlackFast_sound sbCell0765
  · exact checkSingleBlackFast_sound sbCell0766
  · exact checkSingleBlackFast_sound sbCell0767
  · exact checkSingleBlackFast2_sound sbCell0768
  · exact checkSingleBlackFast_sound sbCell0769
  · exact checkSingleBlackFast_sound sbCell0770
  · exact checkSingleBlackFast_sound sbCell0771
  · exact checkSingleBlackFast_sound sbCell0772
  · exact checkSingleBlackFast_sound sbCell0773
  · exact checkSingleBlackFast_sound sbCell0774
  · exact checkSingleBlackFast_sound sbCell0775
  · exact checkSingleBlackFast2_sound sbCell0776

end LangtonsAnt
