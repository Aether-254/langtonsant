import FastCell2
import SingleBlackEarly.C1110
import SingleBlackEarly.C1111
import SingleBlackEarly.C1112
import SingleBlackEarly.C1113
import SingleBlackEarly.C1114
import SingleBlackEarly.C1115
import SingleBlackEarly.C1116
import SingleBlackEarly.C1117
import SingleBlackEarly.C1118
import SingleBlackEarly.C1119
import SingleBlackEarly.C1120
import SingleBlackEarly.C1121
import SingleBlackEarly.C1122
import SingleBlackEarly.C1123
import SingleBlackEarly.C1124
import SingleBlackEarly.C1125
import SingleBlackEarly.C1126
import SingleBlackEarly.C1127
import SingleBlackEarly.C1128
import SingleBlackEarly.C1129
import SingleBlackEarly.C1130
import SingleBlackEarly.C1131
import SingleBlackEarly.C1132
import SingleBlackEarly.C1133
import SingleBlackEarly.C1134
import SingleBlackEarly.C1135
import SingleBlackEarly.C1136
import SingleBlackEarly.C1137
import SingleBlackEarly.C1138
import SingleBlackEarly.C1139
import SingleBlackEarly.C1140
import SingleBlackEarly.C1141
import SingleBlackEarly.C1142
import SingleBlackEarly.C1143
import SingleBlackEarly.C1144
import SingleBlackEarly.C1145
import SingleBlackEarly.C1146

namespace LangtonsAnt

def sbGroup30 : List Point :=
  [(-1, -12), (-1, -11), (1, -12), (1, -13), (0, -13), (2, -13), (2, -14), (1, -14), (2, -12), (25, -12), (25, -13), (24, -17), (24, -18), (23, -18), (25, -18), (25, -19), (24, -19), (25, -17), (26, -17), (26, -18), (26, -16), (27, -16), (27, -17), (25, -16), (20, -18), (19, -18), (19, -17), (21, -18), (21, -19), (20, -19), (22, -19), (22, -20), (21, -20), (22, -18), (19, -19), (18, -19), (18, -18)]

theorem sbGroup30_ok : forall q, q ∈ sbGroup30 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup30, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1110
  · exact checkSingleBlackFast_sound sbCell1111
  · exact checkSingleBlackFast2_sound sbCell1112
  · exact checkSingleBlackFast_sound sbCell1113
  · exact checkSingleBlackFast2_sound sbCell1114
  · exact checkSingleBlackFast_sound sbCell1115
  · exact checkSingleBlackFast_sound sbCell1116
  · exact checkSingleBlackFast_sound sbCell1117
  · exact checkSingleBlackFast_sound sbCell1118
  · exact checkSingleBlackFast_sound sbCell1119
  · exact checkSingleBlackFast_sound sbCell1120
  · exact checkSingleBlackFast_sound sbCell1121
  · exact checkSingleBlackFast_sound sbCell1122
  · exact checkSingleBlackFast_sound sbCell1123
  · exact checkSingleBlackFast2_sound sbCell1124
  · exact checkSingleBlackFast_sound sbCell1125
  · exact checkSingleBlackFast_sound sbCell1126
  · exact checkSingleBlackFast_sound sbCell1127
  · exact checkSingleBlackFast_sound sbCell1128
  · exact checkSingleBlackFast_sound sbCell1129
  · exact checkSingleBlackFast2_sound sbCell1130
  · exact checkSingleBlackFast_sound sbCell1131
  · exact checkSingleBlackFast_sound sbCell1132
  · exact checkSingleBlackFast_sound sbCell1133
  · exact checkSingleBlackFast_sound sbCell1134
  · exact checkSingleBlackFast_sound sbCell1135
  · exact checkSingleBlackFast2_sound sbCell1136
  · exact checkSingleBlackFast_sound sbCell1137
  · exact checkSingleBlackFast2_sound sbCell1138
  · exact checkSingleBlackFast_sound sbCell1139
  · exact checkSingleBlackFast_sound sbCell1140
  · exact checkSingleBlackFast_sound sbCell1141
  · exact checkSingleBlackFast_sound sbCell1142
  · exact checkSingleBlackFast_sound sbCell1143
  · exact checkSingleBlackFast2_sound sbCell1144
  · exact checkSingleBlackFast_sound sbCell1145
  · exact checkSingleBlackFast_sound sbCell1146

end LangtonsAnt
