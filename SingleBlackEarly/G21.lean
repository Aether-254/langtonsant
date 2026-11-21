import FastCell2
import SingleBlackEarly.C0777
import SingleBlackEarly.C0778
import SingleBlackEarly.C0779
import SingleBlackEarly.C0780
import SingleBlackEarly.C0781
import SingleBlackEarly.C0782
import SingleBlackEarly.C0783
import SingleBlackEarly.C0784
import SingleBlackEarly.C0785
import SingleBlackEarly.C0786
import SingleBlackEarly.C0787
import SingleBlackEarly.C0788
import SingleBlackEarly.C0789
import SingleBlackEarly.C0790
import SingleBlackEarly.C0791
import SingleBlackEarly.C0792
import SingleBlackEarly.C0793
import SingleBlackEarly.C0794
import SingleBlackEarly.C0795
import SingleBlackEarly.C0796
import SingleBlackEarly.C0797
import SingleBlackEarly.C0798
import SingleBlackEarly.C0799
import SingleBlackEarly.C0800
import SingleBlackEarly.C0801
import SingleBlackEarly.C0802
import SingleBlackEarly.C0803
import SingleBlackEarly.C0804
import SingleBlackEarly.C0805
import SingleBlackEarly.C0806
import SingleBlackEarly.C0807
import SingleBlackEarly.C0808
import SingleBlackEarly.C0809
import SingleBlackEarly.C0810
import SingleBlackEarly.C0811
import SingleBlackEarly.C0812
import SingleBlackEarly.C0813

namespace LangtonsAnt

def sbGroup21 : List Point :=
  [(24, -15), (24, -16), (24, -14), (25, -14), (25, -15), (23, -14), (24, -13), (24, -10), (25, -10), (25, -11), (23, -10), (23, -9), (24, -9), (24, -8), (25, -8), (25, -9), (23, -8), (23, -7), (24, -7), (24, -6), (25, -6), (25, -7), (23, -6), (23, -5), (24, -5), (22, -5), (22, -4), (23, -4), (22, -6), (21, -6), (21, -5), (21, -4), (24, -4), (25, -4), (25, -5), (25, -3), (26, -3)]

theorem sbGroup21_ok : forall q, q ∈ sbGroup21 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup21, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0777
  · exact checkSingleBlackFast_sound sbCell0778
  · exact checkSingleBlackFast_sound sbCell0779
  · exact checkSingleBlackFast2_sound sbCell0780
  · exact checkSingleBlackFast_sound sbCell0781
  · exact checkSingleBlackFast2_sound sbCell0782
  · exact checkSingleBlackFast_sound sbCell0783
  · exact checkSingleBlackFast_sound sbCell0784
  · exact checkSingleBlackFast_sound sbCell0785
  · exact checkSingleBlackFast_sound sbCell0786
  · exact checkSingleBlackFast_sound sbCell0787
  · exact checkSingleBlackFast2_sound sbCell0788
  · exact checkSingleBlackFast_sound sbCell0789
  · exact checkSingleBlackFast2_sound sbCell0790
  · exact checkSingleBlackFast_sound sbCell0791
  · exact checkSingleBlackFast_sound sbCell0792
  · exact checkSingleBlackFast_sound sbCell0793
  · exact checkSingleBlackFast_sound sbCell0794
  · exact checkSingleBlackFast_sound sbCell0795
  · exact checkSingleBlackFast2_sound sbCell0796
  · exact checkSingleBlackFast_sound sbCell0797
  · exact checkSingleBlackFast_sound sbCell0798
  · exact checkSingleBlackFast_sound sbCell0799
  · exact checkSingleBlackFast2_sound sbCell0800
  · exact checkSingleBlackFast_sound sbCell0801
  · exact checkSingleBlackFast_sound sbCell0802
  · exact checkSingleBlackFast_sound sbCell0803
  · exact checkSingleBlackFast_sound sbCell0804
  · exact checkSingleBlackFast_sound sbCell0805
  · exact checkSingleBlackFast_sound sbCell0806
  · exact checkSingleBlackFast_sound sbCell0807
  · exact checkSingleBlackFast2_sound sbCell0808
  · exact checkSingleBlackFast_sound sbCell0809
  · exact checkSingleBlackFast2_sound sbCell0810
  · exact checkSingleBlackFast_sound sbCell0811
  · exact checkSingleBlackFast2_sound sbCell0812
  · exact checkSingleBlack_sound sbCell0813

end LangtonsAnt
