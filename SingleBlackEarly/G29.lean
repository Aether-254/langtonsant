import FastCell2
import SingleBlackEarly.C1073
import SingleBlackEarly.C1074
import SingleBlackEarly.C1075
import SingleBlackEarly.C1076
import SingleBlackEarly.C1077
import SingleBlackEarly.C1078
import SingleBlackEarly.C1079
import SingleBlackEarly.C1080
import SingleBlackEarly.C1081
import SingleBlackEarly.C1082
import SingleBlackEarly.C1083
import SingleBlackEarly.C1084
import SingleBlackEarly.C1085
import SingleBlackEarly.C1086
import SingleBlackEarly.C1087
import SingleBlackEarly.C1088
import SingleBlackEarly.C1089
import SingleBlackEarly.C1090
import SingleBlackEarly.C1091
import SingleBlackEarly.C1092
import SingleBlackEarly.C1093
import SingleBlackEarly.C1094
import SingleBlackEarly.C1095
import SingleBlackEarly.C1096
import SingleBlackEarly.C1097
import SingleBlackEarly.C1098
import SingleBlackEarly.C1099
import SingleBlackEarly.C1100
import SingleBlackEarly.C1101
import SingleBlackEarly.C1102
import SingleBlackEarly.C1103
import SingleBlackEarly.C1104
import SingleBlackEarly.C1105
import SingleBlackEarly.C1106
import SingleBlackEarly.C1107
import SingleBlackEarly.C1108
import SingleBlackEarly.C1109

namespace LangtonsAnt

def sbGroup29 : List Point :=
  [(-14, -5), (-14, -6), (-15, -6), (-13, -6), (-13, -7), (-14, -7), (-13, -5), (-12, -6), (-9, -6), (-9, -7), (-10, -7), (-9, -5), (-8, -5), (-8, -6), (-3, -7), (-6, -8), (-7, -8), (-7, -7), (-7, -9), (-8, -9), (-8, -8), (-6, -9), (-6, -10), (-7, -10), (-5, -10), (-5, -11), (-6, -11), (-5, -9), (-4, -9), (-4, -10), (0, -10), (-1, -10), (-1, -9), (1, -10), (1, -11), (0, -11), (0, -12)]

theorem sbGroup29_ok : forall q, q ∈ sbGroup29 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup29, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1073
  · exact checkSingleBlackFast_sound sbCell1074
  · exact checkSingleBlackFast_sound sbCell1075
  · exact checkSingleBlackFast_sound sbCell1076
  · exact checkSingleBlackFast_sound sbCell1077
  · exact checkSingleBlackFast2_sound sbCell1078
  · exact checkSingleBlackFast_sound sbCell1079
  · exact checkSingleBlackFast_sound sbCell1080
  · exact checkSingleBlackFast_sound sbCell1081
  · exact checkSingleBlackFast_sound sbCell1082
  · exact checkSingleBlackFast_sound sbCell1083
  · exact checkSingleBlackFast_sound sbCell1084
  · exact checkSingleBlackFast2_sound sbCell1085
  · exact checkSingleBlackFast_sound sbCell1086
  · exact checkSingleBlackFast_sound sbCell1087
  · exact checkSingleBlackFast_sound sbCell1088
  · exact checkSingleBlackFast2_sound sbCell1089
  · exact checkSingleBlackFast2_sound sbCell1090
  · exact checkSingleBlackFast_sound sbCell1091
  · exact checkSingleBlackFast2_sound sbCell1092
  · exact checkSingleBlackFast_sound sbCell1093
  · exact checkSingleBlackFast_sound sbCell1094
  · exact checkSingleBlackFast_sound sbCell1095
  · exact checkSingleBlackFast2_sound sbCell1096
  · exact checkSingleBlackFast_sound sbCell1097
  · exact checkSingleBlackFast_sound sbCell1098
  · exact checkSingleBlackFast_sound sbCell1099
  · exact checkSingleBlackFast2_sound sbCell1100
  · exact checkSingleBlackFast_sound sbCell1101
  · exact checkSingleBlackFast2_sound sbCell1102
  · exact checkSingleBlackFast_sound sbCell1103
  · exact checkSingleBlackFast_sound sbCell1104
  · exact checkSingleBlackFast_sound sbCell1105
  · exact checkSingleBlackFast_sound sbCell1106
  · exact checkSingleBlackFast_sound sbCell1107
  · exact checkSingleBlackFast_sound sbCell1108
  · exact checkSingleBlackFast_sound sbCell1109

end LangtonsAnt
