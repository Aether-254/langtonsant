import FastCell2
import SingleBlackEarly.C1036
import SingleBlackEarly.C1037
import SingleBlackEarly.C1038
import SingleBlackEarly.C1039
import SingleBlackEarly.C1040
import SingleBlackEarly.C1041
import SingleBlackEarly.C1042
import SingleBlackEarly.C1043
import SingleBlackEarly.C1044
import SingleBlackEarly.C1045
import SingleBlackEarly.C1046
import SingleBlackEarly.C1047
import SingleBlackEarly.C1048
import SingleBlackEarly.C1049
import SingleBlackEarly.C1050
import SingleBlackEarly.C1051
import SingleBlackEarly.C1052
import SingleBlackEarly.C1053
import SingleBlackEarly.C1054
import SingleBlackEarly.C1055
import SingleBlackEarly.C1056
import SingleBlackEarly.C1057
import SingleBlackEarly.C1058
import SingleBlackEarly.C1059
import SingleBlackEarly.C1060
import SingleBlackEarly.C1061
import SingleBlackEarly.C1062
import SingleBlackEarly.C1063
import SingleBlackEarly.C1064
import SingleBlackEarly.C1065
import SingleBlackEarly.C1066
import SingleBlackEarly.C1067
import SingleBlackEarly.C1068
import SingleBlackEarly.C1069
import SingleBlackEarly.C1070
import SingleBlackEarly.C1071
import SingleBlackEarly.C1072

namespace LangtonsAnt

def sbGroup28 : List Point :=
  [(-12, 3), (-12, 4), (-12, 2), (-13, 2), (-13, 3), (-11, 2), (-11, -3), (-12, -3), (-12, -2), (-12, -4), (-13, -4), (-13, -3), (-11, -4), (-11, -5), (-12, -5), (-10, -5), (-10, -6), (-11, -6), (-10, -4), (-13, -2), (-13, -1), (-12, -1), (-14, -1), (-14, 0), (-13, 0), (-14, -2), (-15, -2), (-15, -1), (-15, -3), (-16, -3), (-16, -2), (-14, -3), (-14, -4), (-15, -4), (-15, -5), (-16, -5), (-16, -4)]

theorem sbGroup28_ok : forall q, q ∈ sbGroup28 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup28, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1036
  · exact checkSingleBlackFast_sound sbCell1037
  · exact checkSingleBlackFast_sound sbCell1038
  · exact checkSingleBlackFast_sound sbCell1039
  · exact checkSingleBlackFast2_sound sbCell1040
  · exact checkSingleBlackFast_sound sbCell1041
  · exact checkSingleBlackFast2_sound sbCell1042
  · exact checkSingleBlackFast2_sound sbCell1043
  · exact checkSingleBlack_sound sbCell1044
  · exact checkSingleBlackFast_sound sbCell1045
  · exact checkSingleBlackFast2_sound sbCell1046
  · exact checkSingleBlackFast_sound sbCell1047
  · exact checkSingleBlackFast_sound sbCell1048
  · exact checkSingleBlackFast_sound sbCell1049
  · exact checkSingleBlackFast_sound sbCell1050
  · exact checkSingleBlackFast_sound sbCell1051
  · exact checkSingleBlackFast_sound sbCell1052
  · exact checkSingleBlackFast2_sound sbCell1053
  · exact checkSingleBlackFast_sound sbCell1054
  · exact checkSingleBlackFast_sound sbCell1055
  · exact checkSingleBlackFast_sound sbCell1056
  · exact checkSingleBlackFast_sound sbCell1057
  · exact checkSingleBlackFast2_sound sbCell1058
  · exact checkSingleBlackFast_sound sbCell1059
  · exact checkSingleBlackFast2_sound sbCell1060
  · exact checkSingleBlackFast_sound sbCell1061
  · exact checkSingleBlackFast_sound sbCell1062
  · exact checkSingleBlackFast_sound sbCell1063
  · exact checkSingleBlackFast2_sound sbCell1064
  · exact checkSingleBlackFast_sound sbCell1065
  · exact checkSingleBlackFast2_sound sbCell1066
  · exact checkSingleBlackFast_sound sbCell1067
  · exact checkSingleBlackFast_sound sbCell1068
  · exact checkSingleBlackFast_sound sbCell1069
  · exact checkSingleBlackFast_sound sbCell1070
  · exact checkSingleBlackFast_sound sbCell1071
  · exact checkSingleBlackFast2_sound sbCell1072

end LangtonsAnt
