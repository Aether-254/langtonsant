import FastCell2
import SingleBlackEarly.C0703
import SingleBlackEarly.C0704
import SingleBlackEarly.C0705
import SingleBlackEarly.C0706
import SingleBlackEarly.C0707
import SingleBlackEarly.C0708
import SingleBlackEarly.C0709
import SingleBlackEarly.C0710
import SingleBlackEarly.C0711
import SingleBlackEarly.C0712
import SingleBlackEarly.C0713
import SingleBlackEarly.C0714
import SingleBlackEarly.C0715
import SingleBlackEarly.C0716
import SingleBlackEarly.C0717
import SingleBlackEarly.C0718
import SingleBlackEarly.C0719
import SingleBlackEarly.C0720
import SingleBlackEarly.C0721
import SingleBlackEarly.C0722
import SingleBlackEarly.C0723
import SingleBlackEarly.C0724
import SingleBlackEarly.C0725
import SingleBlackEarly.C0726
import SingleBlackEarly.C0727
import SingleBlackEarly.C0728
import SingleBlackEarly.C0729
import SingleBlackEarly.C0730
import SingleBlackEarly.C0731
import SingleBlackEarly.C0732
import SingleBlackEarly.C0733
import SingleBlackEarly.C0734
import SingleBlackEarly.C0735
import SingleBlackEarly.C0736
import SingleBlackEarly.C0737
import SingleBlackEarly.C0738
import SingleBlackEarly.C0739

namespace LangtonsAnt

def sbGroup19 : List Point :=
  [(22, -8), (20, -7), (2, -9), (1, -9), (0, -9), (0, -8), (3, -11), (2, -11), (2, -10), (4, -11), (4, -12), (3, -12), (5, -12), (5, -13), (4, -13), (5, -11), (6, -11), (6, -12), (7, -11), (7, -12), (7, -13), (6, -13), (8, -13), (8, -14), (7, -14), (8, -12), (13, -12), (13, -13), (12, -13), (14, -13), (14, -14), (13, -14), (14, -12), (17, -12), (17, -13), (16, -13), (18, -13)]

theorem sbGroup19_ok : forall q, q ∈ sbGroup19 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup19, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0703
  · exact checkSingleBlackFast_sound sbCell0704
  · exact checkSingleBlackFast_sound sbCell0705
  · exact checkSingleBlackFast_sound sbCell0706
  · exact checkSingleBlackFast_sound sbCell0707
  · exact checkSingleBlackFast2_sound sbCell0708
  · exact checkSingleBlackFast_sound sbCell0709
  · exact checkSingleBlackFast2_sound sbCell0710
  · exact checkSingleBlackFast_sound sbCell0711
  · exact checkSingleBlackFast_sound sbCell0712
  · exact checkSingleBlackFast_sound sbCell0713
  · exact checkSingleBlackFast_sound sbCell0714
  · exact checkSingleBlackFast_sound sbCell0715
  · exact checkSingleBlackFast_sound sbCell0716
  · exact checkSingleBlackFast_sound sbCell0717
  · exact checkSingleBlackFast_sound sbCell0718
  · exact checkSingleBlackFast_sound sbCell0719
  · exact checkSingleBlackFast2_sound sbCell0720
  · exact checkSingleBlackFast_sound sbCell0721
  · exact checkSingleBlackFast_sound sbCell0722
  · exact checkSingleBlackFast_sound sbCell0723
  · exact checkSingleBlackFast2_sound sbCell0724
  · exact checkSingleBlackFast_sound sbCell0725
  · exact checkSingleBlackFast2_sound sbCell0726
  · exact checkSingleBlackFast_sound sbCell0727
  · exact checkSingleBlackFast2_sound sbCell0728
  · exact checkSingleBlackFast_sound sbCell0729
  · exact checkSingleBlackFast_sound sbCell0730
  · exact checkSingleBlackFast_sound sbCell0731
  · exact checkSingleBlackFast_sound sbCell0732
  · exact checkSingleBlackFast_sound sbCell0733
  · exact checkSingleBlackFast_sound sbCell0734
  · exact checkSingleBlackFast_sound sbCell0735
  · exact checkSingleBlackFast_sound sbCell0736
  · exact checkSingleBlackFast_sound sbCell0737
  · exact checkSingleBlackFast2_sound sbCell0738
  · exact checkSingleBlackFast_sound sbCell0739

end LangtonsAnt
