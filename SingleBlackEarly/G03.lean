import FastCell2
import SingleBlackEarly.C0111
import SingleBlackEarly.C0112
import SingleBlackEarly.C0113
import SingleBlackEarly.C0114
import SingleBlackEarly.C0115
import SingleBlackEarly.C0116
import SingleBlackEarly.C0117
import SingleBlackEarly.C0118
import SingleBlackEarly.C0119
import SingleBlackEarly.C0120
import SingleBlackEarly.C0121
import SingleBlackEarly.C0122
import SingleBlackEarly.C0123
import SingleBlackEarly.C0124
import SingleBlackEarly.C0125
import SingleBlackEarly.C0126
import SingleBlackEarly.C0127
import SingleBlackEarly.C0128
import SingleBlackEarly.C0129
import SingleBlackEarly.C0130
import SingleBlackEarly.C0131
import SingleBlackEarly.C0132
import SingleBlackEarly.C0133
import SingleBlackEarly.C0134
import SingleBlackEarly.C0135
import SingleBlackEarly.C0136
import SingleBlackEarly.C0137
import SingleBlackEarly.C0138
import SingleBlackEarly.C0139
import SingleBlackEarly.C0140
import SingleBlackEarly.C0141
import SingleBlackEarly.C0142
import SingleBlackEarly.C0143
import SingleBlackEarly.C0144
import SingleBlackEarly.C0145
import SingleBlackEarly.C0146
import SingleBlackEarly.C0147

namespace LangtonsAnt

def sbGroup03 : List Point :=
  [(4, 1), (4, 0), (-4, -1), (-4, 0), (5, 5), (6, 5), (6, 4), (6, 6), (7, 6), (7, 5), (5, 6), (5, 7), (6, 7), (4, 7), (4, 8), (5, 8), (4, 6), (5, 2), (5, 1), (5, 0), (5, -1), (6, -1), (6, -2), (5, -2), (6, 0), (7, 0), (7, -1), (7, 1), (8, 1), (8, 0), (6, 1), (6, 2), (7, 2), (7, 3), (8, 3), (8, 2), (6, 3)]

theorem sbGroup03_ok : forall q, q ∈ sbGroup03 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup03, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0111
  · exact checkSingleBlackFast_sound sbCell0112
  · exact checkSingleBlackFast_sound sbCell0113
  · exact checkSingleBlackFast_sound sbCell0114
  · exact checkSingleBlackFast_sound sbCell0115
  · exact checkSingleBlackFast_sound sbCell0116
  · exact checkSingleBlackFast_sound sbCell0117
  · exact checkSingleBlackFast_sound sbCell0118
  · exact checkSingleBlackFast_sound sbCell0119
  · exact checkSingleBlackFast_sound sbCell0120
  · exact checkSingleBlackFast_sound sbCell0121
  · exact checkSingleBlackFast_sound sbCell0122
  · exact checkSingleBlackFast_sound sbCell0123
  · exact checkSingleBlackFast_sound sbCell0124
  · exact checkSingleBlackFast_sound sbCell0125
  · exact checkSingleBlackFast_sound sbCell0126
  · exact checkSingleBlackFast_sound sbCell0127
  · exact checkSingleBlackFast_sound sbCell0128
  · exact checkSingleBlackFast_sound sbCell0129
  · exact checkSingleBlackFast_sound sbCell0130
  · exact checkSingleBlackFast_sound sbCell0131
  · exact checkSingleBlackFast2_sound sbCell0132
  · exact checkSingleBlackFast_sound sbCell0133
  · exact checkSingleBlackFast_sound sbCell0134
  · exact checkSingleBlackFast_sound sbCell0135
  · exact checkSingleBlackFast2_sound sbCell0136
  · exact checkSingleBlackFast_sound sbCell0137
  · exact checkSingleBlackFast_sound sbCell0138
  · exact checkSingleBlackFast_sound sbCell0139
  · exact checkSingleBlackFast_sound sbCell0140
  · exact checkSingleBlackFast_sound sbCell0141
  · exact checkSingleBlackFast_sound sbCell0142
  · exact checkSingleBlackFast_sound sbCell0143
  · exact checkSingleBlackFast_sound sbCell0144
  · exact checkSingleBlackFast_sound sbCell0145
  · exact checkSingleBlackFast_sound sbCell0146
  · exact checkSingleBlackFast_sound sbCell0147

end LangtonsAnt
