import FastCell2
import SingleBlackEarly.C0000
import SingleBlackEarly.C0001
import SingleBlackEarly.C0002
import SingleBlackEarly.C0003
import SingleBlackEarly.C0004
import SingleBlackEarly.C0005
import SingleBlackEarly.C0006
import SingleBlackEarly.C0007
import SingleBlackEarly.C0008
import SingleBlackEarly.C0009
import SingleBlackEarly.C0010
import SingleBlackEarly.C0011
import SingleBlackEarly.C0012
import SingleBlackEarly.C0013
import SingleBlackEarly.C0014
import SingleBlackEarly.C0015
import SingleBlackEarly.C0016
import SingleBlackEarly.C0017
import SingleBlackEarly.C0018
import SingleBlackEarly.C0019
import SingleBlackEarly.C0020
import SingleBlackEarly.C0021
import SingleBlackEarly.C0022
import SingleBlackEarly.C0023
import SingleBlackEarly.C0024
import SingleBlackEarly.C0025
import SingleBlackEarly.C0026
import SingleBlackEarly.C0027
import SingleBlackEarly.C0028
import SingleBlackEarly.C0029
import SingleBlackEarly.C0030
import SingleBlackEarly.C0031
import SingleBlackEarly.C0032
import SingleBlackEarly.C0033
import SingleBlackEarly.C0034
import SingleBlackEarly.C0035
import SingleBlackEarly.C0036

namespace LangtonsAnt

def sbGroup00 : List Point :=
  [(0, 0), (1, 0), (1, -1), (0, -1), (-1, 0), (-1, 1), (0, 1), (-1, -1), (-2, -1), (-2, 0), (-2, -2), (-3, -2), (-3, -1), (-1, -2), (-1, -3), (-2, -3), (0, -3), (0, -4), (-1, -4), (0, -2), (1, -2), (1, -3), (1, 1), (2, 1), (2, 0), (2, 2), (3, 2), (3, 1), (1, 2), (1, 3), (2, 3), (0, 3), (0, 4), (1, 4), (0, 2), (-1, 2), (-1, 3)]

theorem sbGroup00_ok : forall q, q ∈ sbGroup00 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup00, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0000
  · exact checkSingleBlackFast_sound sbCell0001
  · exact checkSingleBlackFast_sound sbCell0002
  · exact checkSingleBlackFast_sound sbCell0003
  · exact checkSingleBlackFast2_sound sbCell0004
  · exact checkSingleBlackFast_sound sbCell0005
  · exact checkSingleBlackFast_sound sbCell0006
  · exact checkSingleBlackFast_sound sbCell0007
  · exact checkSingleBlackFast_sound sbCell0008
  · exact checkSingleBlackFast_sound sbCell0009
  · exact checkSingleBlackFast_sound sbCell0010
  · exact checkSingleBlackFast_sound sbCell0011
  · exact checkSingleBlackFast2_sound sbCell0012
  · exact checkSingleBlackFast_sound sbCell0013
  · exact checkSingleBlackFast_sound sbCell0014
  · exact checkSingleBlackFast_sound sbCell0015
  · exact checkSingleBlackFast_sound sbCell0016
  · exact checkSingleBlackFast_sound sbCell0017
  · exact checkSingleBlack_sound sbCell0018
  · exact checkSingleBlackFast_sound sbCell0019
  · exact checkSingleBlackFast_sound sbCell0020
  · exact checkSingleBlackFast_sound sbCell0021
  · exact checkSingleBlackFast_sound sbCell0022
  · exact checkSingleBlackFast_sound sbCell0023
  · exact checkSingleBlackFast_sound sbCell0024
  · exact checkSingleBlackFast_sound sbCell0025
  · exact checkSingleBlackFast_sound sbCell0026
  · exact checkSingleBlackFast_sound sbCell0027
  · exact checkSingleBlackFast_sound sbCell0028
  · exact checkSingleBlackFast_sound sbCell0029
  · exact checkSingleBlackFast_sound sbCell0030
  · exact checkSingleBlackFast_sound sbCell0031
  · exact checkSingleBlackFast_sound sbCell0032
  · exact checkSingleBlackFast_sound sbCell0033
  · exact checkSingleBlackFast_sound sbCell0034
  · exact checkSingleBlack_sound sbCell0035
  · exact checkSingleBlackFast_sound sbCell0036

end LangtonsAnt
