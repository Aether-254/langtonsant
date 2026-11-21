import FastCell2
import SingleBlackEarly.C0074
import SingleBlackEarly.C0075
import SingleBlackEarly.C0076
import SingleBlackEarly.C0077
import SingleBlackEarly.C0078
import SingleBlackEarly.C0079
import SingleBlackEarly.C0080
import SingleBlackEarly.C0081
import SingleBlackEarly.C0082
import SingleBlackEarly.C0083
import SingleBlackEarly.C0084
import SingleBlackEarly.C0085
import SingleBlackEarly.C0086
import SingleBlackEarly.C0087
import SingleBlackEarly.C0088
import SingleBlackEarly.C0089
import SingleBlackEarly.C0090
import SingleBlackEarly.C0091
import SingleBlackEarly.C0092
import SingleBlackEarly.C0093
import SingleBlackEarly.C0094
import SingleBlackEarly.C0095
import SingleBlackEarly.C0096
import SingleBlackEarly.C0097
import SingleBlackEarly.C0098
import SingleBlackEarly.C0099
import SingleBlackEarly.C0100
import SingleBlackEarly.C0101
import SingleBlackEarly.C0102
import SingleBlackEarly.C0103
import SingleBlackEarly.C0104
import SingleBlackEarly.C0105
import SingleBlackEarly.C0106
import SingleBlackEarly.C0107
import SingleBlackEarly.C0108
import SingleBlackEarly.C0109
import SingleBlackEarly.C0110

namespace LangtonsAnt

def sbGroup02 : List Point :=
  [(2, -5), (4, -5), (4, -6), (3, -6), (4, -4), (5, -4), (5, -5), (5, -3), (6, -3), (6, -4), (4, -3), (3, 3), (4, 3), (4, 2), (4, 4), (5, 4), (5, 3), (3, 4), (3, 5), (4, 5), (2, 5), (2, 6), (3, 6), (2, 4), (-3, 4), (-3, 5), (-2, 5), (-4, 5), (-4, 6), (-3, 6), (-4, 4), (-5, 4), (-5, 5), (-5, 3), (-6, 3), (-6, 4), (-4, 3)]

theorem sbGroup02_ok : forall q, q ∈ sbGroup02 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup02, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0074
  · exact checkSingleBlackFast_sound sbCell0075
  · exact checkSingleBlackFast_sound sbCell0076
  · exact checkSingleBlackFast_sound sbCell0077
  · exact checkSingleBlackFast_sound sbCell0078
  · exact checkSingleBlackFast_sound sbCell0079
  · exact checkSingleBlackFast_sound sbCell0080
  · exact checkSingleBlackFast_sound sbCell0081
  · exact checkSingleBlackFast_sound sbCell0082
  · exact checkSingleBlackFast_sound sbCell0083
  · exact checkSingleBlackFast2_sound sbCell0084
  · exact checkSingleBlackFast_sound sbCell0085
  · exact checkSingleBlackFast_sound sbCell0086
  · exact checkSingleBlackFast_sound sbCell0087
  · exact checkSingleBlackFast_sound sbCell0088
  · exact checkSingleBlackFast_sound sbCell0089
  · exact checkSingleBlack_sound sbCell0090
  · exact checkSingleBlackFast_sound sbCell0091
  · exact checkSingleBlackFast_sound sbCell0092
  · exact checkSingleBlackFast_sound sbCell0093
  · exact checkSingleBlackFast_sound sbCell0094
  · exact checkSingleBlackFast_sound sbCell0095
  · exact checkSingleBlackFast_sound sbCell0096
  · exact checkSingleBlackFast_sound sbCell0097
  · exact checkSingleBlackFast_sound sbCell0098
  · exact checkSingleBlackFast_sound sbCell0099
  · exact checkSingleBlackFast_sound sbCell0100
  · exact checkSingleBlackFast_sound sbCell0101
  · exact checkSingleBlackFast_sound sbCell0102
  · exact checkSingleBlackFast2_sound sbCell0103
  · exact checkSingleBlackFast2_sound sbCell0104
  · exact checkSingleBlackFast_sound sbCell0105
  · exact checkSingleBlackFast_sound sbCell0106
  · exact checkSingleBlackFast_sound sbCell0107
  · exact checkSingleBlackFast_sound sbCell0108
  · exact checkSingleBlackFast_sound sbCell0109
  · exact checkSingleBlackFast_sound sbCell0110

end LangtonsAnt
