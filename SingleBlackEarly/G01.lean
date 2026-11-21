import FastCell2
import SingleBlackEarly.C0037
import SingleBlackEarly.C0038
import SingleBlackEarly.C0039
import SingleBlackEarly.C0040
import SingleBlackEarly.C0041
import SingleBlackEarly.C0042
import SingleBlackEarly.C0043
import SingleBlackEarly.C0044
import SingleBlackEarly.C0045
import SingleBlackEarly.C0046
import SingleBlackEarly.C0047
import SingleBlackEarly.C0048
import SingleBlackEarly.C0049
import SingleBlackEarly.C0050
import SingleBlackEarly.C0051
import SingleBlackEarly.C0052
import SingleBlackEarly.C0053
import SingleBlackEarly.C0054
import SingleBlackEarly.C0055
import SingleBlackEarly.C0056
import SingleBlackEarly.C0057
import SingleBlackEarly.C0058
import SingleBlackEarly.C0059
import SingleBlackEarly.C0060
import SingleBlackEarly.C0061
import SingleBlackEarly.C0062
import SingleBlackEarly.C0063
import SingleBlackEarly.C0064
import SingleBlackEarly.C0065
import SingleBlackEarly.C0066
import SingleBlackEarly.C0067
import SingleBlackEarly.C0068
import SingleBlackEarly.C0069
import SingleBlackEarly.C0070
import SingleBlackEarly.C0071
import SingleBlackEarly.C0072
import SingleBlackEarly.C0073

namespace LangtonsAnt

def sbGroup01 : List Point :=
  [(-2, 3), (-2, 4), (-1, 4), (-2, 2), (-3, 2), (-3, 3), (-3, 1), (-4, 1), (-4, 2), (-2, 1), (-3, 0), (2, -3), (2, -4), (1, -4), (2, -2), (3, -2), (3, -3), (3, -1), (4, -1), (4, -2), (2, -1), (3, 0), (-3, -3), (-4, -3), (-4, -2), (-4, -4), (-5, -4), (-5, -3), (-3, -4), (-3, -5), (-4, -5), (-2, -5), (-2, -6), (-3, -6), (-2, -4), (3, -4), (3, -5)]

theorem sbGroup01_ok : forall q, q ∈ sbGroup01 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup01, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0037
  · exact checkSingleBlackFast_sound sbCell0038
  · exact checkSingleBlackFast_sound sbCell0039
  · exact checkSingleBlackFast_sound sbCell0040
  · exact checkSingleBlackFast_sound sbCell0041
  · exact checkSingleBlackFast_sound sbCell0042
  · exact checkSingleBlackFast_sound sbCell0043
  · exact checkSingleBlackFast_sound sbCell0044
  · exact checkSingleBlackFast_sound sbCell0045
  · exact checkSingleBlackFast_sound sbCell0046
  · exact checkSingleBlackFast_sound sbCell0047
  · exact checkSingleBlackFast_sound sbCell0048
  · exact checkSingleBlackFast_sound sbCell0049
  · exact checkSingleBlackFast_sound sbCell0050
  · exact checkSingleBlackFast_sound sbCell0051
  · exact checkSingleBlackFast2_sound sbCell0052
  · exact checkSingleBlackFast_sound sbCell0053
  · exact checkSingleBlackFast_sound sbCell0054
  · exact checkSingleBlackFast_sound sbCell0055
  · exact checkSingleBlack_sound sbCell0056
  · exact checkSingleBlackFast_sound sbCell0057
  · exact checkSingleBlackFast_sound sbCell0058
  · exact checkSingleBlackFast_sound sbCell0059
  · exact checkSingleBlackFast_sound sbCell0060
  · exact checkSingleBlackFast_sound sbCell0061
  · exact checkSingleBlackFast_sound sbCell0062
  · exact checkSingleBlackFast_sound sbCell0063
  · exact checkSingleBlackFast_sound sbCell0064
  · exact checkSingleBlackFast_sound sbCell0065
  · exact checkSingleBlackFast_sound sbCell0066
  · exact checkSingleBlackFast_sound sbCell0067
  · exact checkSingleBlackFast_sound sbCell0068
  · exact checkSingleBlackFast_sound sbCell0069
  · exact checkSingleBlackFast_sound sbCell0070
  · exact checkSingleBlackFast_sound sbCell0071
  · exact checkSingleBlackFast_sound sbCell0072
  · exact checkSingleBlackFast_sound sbCell0073

end LangtonsAnt
