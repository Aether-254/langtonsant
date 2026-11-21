import FastCell2
import SingleBlackEarly.C0925
import SingleBlackEarly.C0926
import SingleBlackEarly.C0927
import SingleBlackEarly.C0928
import SingleBlackEarly.C0929
import SingleBlackEarly.C0930
import SingleBlackEarly.C0931
import SingleBlackEarly.C0932
import SingleBlackEarly.C0933
import SingleBlackEarly.C0934
import SingleBlackEarly.C0935
import SingleBlackEarly.C0936
import SingleBlackEarly.C0937
import SingleBlackEarly.C0938
import SingleBlackEarly.C0939
import SingleBlackEarly.C0940
import SingleBlackEarly.C0941
import SingleBlackEarly.C0942
import SingleBlackEarly.C0943
import SingleBlackEarly.C0944
import SingleBlackEarly.C0945
import SingleBlackEarly.C0946
import SingleBlackEarly.C0947
import SingleBlackEarly.C0948
import SingleBlackEarly.C0949
import SingleBlackEarly.C0950
import SingleBlackEarly.C0951
import SingleBlackEarly.C0952
import SingleBlackEarly.C0953
import SingleBlackEarly.C0954
import SingleBlackEarly.C0955
import SingleBlackEarly.C0956
import SingleBlackEarly.C0957
import SingleBlackEarly.C0958
import SingleBlackEarly.C0959
import SingleBlackEarly.C0960
import SingleBlackEarly.C0961

namespace LangtonsAnt

def sbGroup25 : List Point :=
  [(-12, 13), (-12, 14), (-11, 14), (-12, 12), (-13, 12), (-13, 13), (-13, 11), (-14, 11), (-14, 12), (-12, 11), (-13, 10), (-8, 12), (-8, 13), (-8, 14), (-7, 14), (21, 7), (22, 7), (22, 6), (20, 7), (20, 8), (21, 8), (20, 9), (17, 15), (13, 16), (13, 17), (14, 17), (13, 15), (6, 16), (7, 16), (7, 17), (8, 17), (8, 16), (6, 17), (6, 18), (7, 18), (5, 18), (5, 19)]

theorem sbGroup25_ok : forall q, q ∈ sbGroup25 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup25, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0925
  · exact checkSingleBlack_sound sbCell0926
  · exact checkSingleBlackFast_sound sbCell0927
  · exact checkSingleBlackFast_sound sbCell0928
  · exact checkSingleBlackFast_sound sbCell0929
  · exact checkSingleBlackFast_sound sbCell0930
  · exact checkSingleBlackFast2_sound sbCell0931
  · exact checkSingleBlackFast2_sound sbCell0932
  · exact checkSingleBlackFast_sound sbCell0933
  · exact checkSingleBlackFast_sound sbCell0934
  · exact checkSingleBlackFast_sound sbCell0935
  · exact checkSingleBlackFast_sound sbCell0936
  · exact checkSingleBlackFast_sound sbCell0937
  · exact checkSingleBlackFast_sound sbCell0938
  · exact checkSingleBlackFast_sound sbCell0939
  · exact checkSingleBlackFast2_sound sbCell0940
  · exact checkSingleBlackFast_sound sbCell0941
  · exact checkSingleBlackFast_sound sbCell0942
  · exact checkSingleBlackFast_sound sbCell0943
  · exact checkSingleBlackFast_sound sbCell0944
  · exact checkSingleBlackFast_sound sbCell0945
  · exact checkSingleBlackFast_sound sbCell0946
  · exact checkSingleBlackFast_sound sbCell0947
  · exact checkSingleBlackFast_sound sbCell0948
  · exact checkSingleBlackFast2_sound sbCell0949
  · exact checkSingleBlackFast_sound sbCell0950
  · exact checkSingleBlackFast2_sound sbCell0951
  · exact checkSingleBlackFast_sound sbCell0952
  · exact checkSingleBlackFast_sound sbCell0953
  · exact checkSingleBlackFast_sound sbCell0954
  · exact checkSingleBlackFast_sound sbCell0955
  · exact checkSingleBlackFast2_sound sbCell0956
  · exact checkSingleBlackFast2_sound sbCell0957
  · exact checkSingleBlackFast_sound sbCell0958
  · exact checkSingleBlackFast_sound sbCell0959
  · exact checkSingleBlackFast_sound sbCell0960
  · exact checkSingleBlackFast_sound sbCell0961

end LangtonsAnt
