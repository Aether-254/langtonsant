import FastCell2
import SegmentCheck
import SingleBlackEarly.C0888
import SingleBlackEarly.C0889
import SingleBlackEarly.C0890
import SingleBlackEarly.C0891
import SingleBlackEarly.C0892
import SingleBlackEarly.C0893
import SingleBlackEarly.C0894
import SingleBlackEarly.C0895
import SingleBlackEarly.C0896
import SingleBlackEarly.C0897
import SingleBlackEarly.C0898
import SingleBlackEarly.C0899
import SingleBlackEarly.C0900
import SingleBlackEarly.C0901
import SingleBlackEarly.C0902
import SingleBlackEarly.C0903
import SingleBlackEarly.C0904
import SingleBlackEarly.C0905
import SingleBlackEarly.C0906
import SingleBlackEarly.C0907
import SingleBlackEarly.C0908
import SingleBlackEarly.C0909
import SingleBlackEarly.C0910
import SingleBlackEarly.C0911
import SingleBlackEarly.C0912
import SingleBlackEarly.C0913
import SingleBlackEarly.C0914
import SingleBlackEarly.C0915
import SingleBlackEarly.C0916
import SingleBlackEarly.C0917
import SingleBlackEarly.C0918
import SingleBlackEarly.C0919
import SingleBlackEarly.C0920
import SingleBlackEarly.C0921
import SingleBlackEarly.C0922
import SingleBlackEarly.C0923
import SingleBlackEarly.C0924

namespace LangtonsAnt

def sbGroup24 : List Point :=
  [(-8, -3), (-8, -4), (-9, -4), (-8, -2), (-7, -2), (-7, -3), (-7, -4), (-6, 10), (-9, 10), (-9, 11), (-8, 11), (-10, 11), (-10, 12), (-9, 12), (-10, 10), (-11, 10), (-11, 11), (-11, 9), (-12, 9), (-12, 10), (-10, 9), (-9, 5), (-10, 5), (-10, 6), (-10, 4), (-11, 4), (-11, 5), (-9, 4), (-10, 3), (-7, 12), (-7, 13), (-6, 13), (-7, 11), (-11, 8), (-11, 12), (-11, 13), (-10, 13)]

theorem sbGroup24_ok : forall q, q ∈ sbGroup24 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup24, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlack_sound sbCell0888
  · exact checkSingleBlackFast_sound sbCell0889
  · exact checkSingleBlack_sound sbCell0890
  · exact checkSingleBlackFast2_sound sbCell0891
  · exact checkSingleBlackFast_sound sbCell0892
  · exact checkSingleBlackFast2_sound sbCell0893
  · exact checkSingleBlackFast2_sound sbCell0894
  · exact checkSingleBlackFast_sound sbCell0895
  · exact checkSingleBlackFast_sound sbCell0896
  · exact checkSingleBlackFast_sound sbCell0897
  · exact checkSingleBlack_sound sbCell0898
  · exact checkSingleBlackFast_sound sbCell0899
  · exact checkSingleBlackFast_sound sbCell0900
  · exact checkSingleBlackFast_sound sbCell0901
  · exact checkSingleBlackFast2_sound sbCell0902
  · exact checkSingleBlackFast_sound sbCell0903
  · exact checkSingleBlackFast2_sound sbCell0904
  · exact checkSingleBlackFast_sound sbCell0905
  · exact checkSingleBlack_sound sbCell0906
  · exact checkSingleBlackFast2_sound sbCell0907
  · exact checkSingleBlackFast_sound sbCell0908
  · exact checkSingleBlackFast_sound sbCell0909
  · exact checkSingleBlackFast_sound sbCell0910
  · exact checkSingleBlackFast_sound sbCell0911
  · exact checkSingleBlackFast2_sound sbCell0912
  · exact checkSingleBlackFast2_sound sbCell0913
  · exact checkSingleBlack_sound sbCell0914
  · exact checkSingleBlackFast_sound sbCell0915
  · exact checkSingleBlackFast_sound sbCell0916
  · exact checkSingleBlackFast_sound sbCell0917
  · exact checkSingleBlackFast_sound sbCell0918
  · exact checkSingleBlackFast_sound sbCell0919
  · exact checkSingleBlackFast_sound sbCell0920
  · exact checkSingleBlackFast_sound sbCell0921
  · exact checkSingleBlackFast2_sound sbCell0922
  · exact sbCell0923
  · exact checkSingleBlack_sound sbCell0924

end LangtonsAnt
