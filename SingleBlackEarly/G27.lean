import FastCell2
import SegmentCheck
import SingleBlackEarly.C0999
import SingleBlackEarly.C1000
import SingleBlackEarly.C1001
import SingleBlackEarly.C1002
import SingleBlackEarly.C1003
import SingleBlackEarly.C1004
import SingleBlackEarly.C1005
import SingleBlackEarly.C1006
import SingleBlackEarly.C1007
import SingleBlackEarly.C1008
import SingleBlackEarly.C1009
import SingleBlackEarly.C1010
import SingleBlackEarly.C1011
import SingleBlackEarly.C1012
import SingleBlackEarly.C1013
import SingleBlackEarly.C1014
import SingleBlackEarly.C1015
import SingleBlackEarly.C1016
import SingleBlackEarly.C1017
import SingleBlackEarly.C1018
import SingleBlackEarly.C1019
import SingleBlackEarly.C1020
import SingleBlackEarly.C1021
import SingleBlackEarly.C1022
import SingleBlackEarly.C1023
import SingleBlackEarly.C1024
import SingleBlackEarly.C1025
import SingleBlackEarly.C1026
import SingleBlackEarly.C1027
import SingleBlackEarly.C1028
import SingleBlackEarly.C1029
import SingleBlackEarly.C1030
import SingleBlackEarly.C1031
import SingleBlackEarly.C1032
import SingleBlackEarly.C1033
import SingleBlackEarly.C1034
import SingleBlackEarly.C1035

namespace LangtonsAnt

def sbGroup27 : List Point :=
  [(-8, 15), (-9, 13), (-13, 9), (-14, 9), (-14, 10), (-14, 8), (-15, 8), (-15, 9), (-13, 8), (-13, 7), (-14, 7), (-12, 7), (-12, 6), (-13, 6), (-12, 8), (-11, 6), (-11, 7), (-5, 14), (-5, 15), (-5, 18), (-5, 19), (-4, 19), (-6, 19), (-6, 20), (-5, 20), (-6, 18), (-7, 18), (-7, 19), (-7, 17), (-8, 17), (-8, 18), (-6, 17), (-6, 16), (-7, 16), (-6, 15), (-6, 14), (-11, 3)]

theorem sbGroup27_ok : forall q, q ∈ sbGroup27 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup27, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0999
  · exact checkSingleBlackFast2_sound sbCell1000
  · exact checkSingleBlackFast_sound sbCell1001
  · exact checkSingleBlackFast2_sound sbCell1002
  · exact checkSingleBlackFast2_sound sbCell1003
  · exact checkSingleBlackFast_sound sbCell1004
  · exact checkSingleBlackFast_sound sbCell1005
  · exact checkSingleBlackFast2_sound sbCell1006
  · exact checkSingleBlackFast_sound sbCell1007
  · exact checkSingleBlackFast2_sound sbCell1008
  · exact checkSingleBlackFast_sound sbCell1009
  · exact checkSingleBlackFast2_sound sbCell1010
  · exact checkSingleBlackFast_sound sbCell1011
  · exact sbCell1012
  · exact checkSingleBlackFast_sound sbCell1013
  · exact checkSingleBlack_sound sbCell1014
  · exact checkSingleBlackFast_sound sbCell1015
  · exact checkSingleBlackFast2_sound sbCell1016
  · exact checkSingleBlackFast_sound sbCell1017
  · exact checkSingleBlackFast_sound sbCell1018
  · exact checkSingleBlackFast_sound sbCell1019
  · exact checkSingleBlackFast_sound sbCell1020
  · exact checkSingleBlackFast_sound sbCell1021
  · exact checkSingleBlack_sound sbCell1022
  · exact checkSingleBlackFast_sound sbCell1023
  · exact checkSingleBlackFast2_sound sbCell1024
  · exact checkSingleBlackFast_sound sbCell1025
  · exact checkSingleBlackFast_sound sbCell1026
  · exact checkSingleBlackFast_sound sbCell1027
  · exact checkSingleBlack_sound sbCell1028
  · exact checkSingleBlackFast_sound sbCell1029
  · exact checkSingleBlackFast2_sound sbCell1030
  · exact checkSingleBlackFast_sound sbCell1031
  · exact checkSingleBlackFast_sound sbCell1032
  · exact checkSingleBlackFast_sound sbCell1033
  · exact checkSingleBlackFast_sound sbCell1034
  · exact checkSingleBlackFast2_sound sbCell1035

end LangtonsAnt
