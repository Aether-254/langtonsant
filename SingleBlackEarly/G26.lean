import FastCell2
import SingleBlackEarly.C0962
import SingleBlackEarly.C0963
import SingleBlackEarly.C0964
import SingleBlackEarly.C0965
import SingleBlackEarly.C0966
import SingleBlackEarly.C0967
import SingleBlackEarly.C0968
import SingleBlackEarly.C0969
import SingleBlackEarly.C0970
import SingleBlackEarly.C0971
import SingleBlackEarly.C0972
import SingleBlackEarly.C0973
import SingleBlackEarly.C0974
import SingleBlackEarly.C0975
import SingleBlackEarly.C0976
import SingleBlackEarly.C0977
import SingleBlackEarly.C0978
import SingleBlackEarly.C0979
import SingleBlackEarly.C0980
import SingleBlackEarly.C0981
import SingleBlackEarly.C0982
import SingleBlackEarly.C0983
import SingleBlackEarly.C0984
import SingleBlackEarly.C0985
import SingleBlackEarly.C0986
import SingleBlackEarly.C0987
import SingleBlackEarly.C0988
import SingleBlackEarly.C0989
import SingleBlackEarly.C0990
import SingleBlackEarly.C0991
import SingleBlackEarly.C0992
import SingleBlackEarly.C0993
import SingleBlackEarly.C0994
import SingleBlackEarly.C0995
import SingleBlackEarly.C0996
import SingleBlackEarly.C0997
import SingleBlackEarly.C0998

namespace LangtonsAnt

def sbGroup26 : List Point :=
  [(6, 19), (5, 17), (4, 17), (4, 18), (3, 18), (3, 19), (4, 19), (3, 17), (2, 17), (2, 18), (2, 16), (3, 16), (1, 18), (1, 19), (2, 19), (1, 17), (0, 17), (0, 18), (-1, 18), (-1, 19), (0, 19), (-1, 17), (-2, 17), (-2, 18), (-3, 18), (-3, 19), (-2, 19), (-3, 17), (-4, 17), (-4, 18), (-4, 16), (-5, 16), (-5, 17), (-3, 16), (-4, 15), (-9, 14), (-9, 15)]

theorem sbGroup26_ok : forall q, q ∈ sbGroup26 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup26, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlack_sound sbCell0962
  · exact checkSingleBlackFast_sound sbCell0963
  · exact checkSingleBlackFast_sound sbCell0964
  · exact checkSingleBlackFast_sound sbCell0965
  · exact checkSingleBlackFast_sound sbCell0966
  · exact checkSingleBlackFast_sound sbCell0967
  · exact checkSingleBlackFast_sound sbCell0968
  · exact checkSingleBlackFast_sound sbCell0969
  · exact checkSingleBlackFast2_sound sbCell0970
  · exact checkSingleBlackFast_sound sbCell0971
  · exact checkSingleBlackFast_sound sbCell0972
  · exact checkSingleBlackFast_sound sbCell0973
  · exact checkSingleBlackFast2_sound sbCell0974
  · exact checkSingleBlackFast_sound sbCell0975
  · exact checkSingleBlackFast_sound sbCell0976
  · exact checkSingleBlackFast_sound sbCell0977
  · exact checkSingleBlackFast_sound sbCell0978
  · exact checkSingleBlackFast_sound sbCell0979
  · exact checkSingleBlackFast_sound sbCell0980
  · exact checkSingleBlackFast_sound sbCell0981
  · exact checkSingleBlackFast_sound sbCell0982
  · exact checkSingleBlackFast_sound sbCell0983
  · exact checkSingleBlackFast_sound sbCell0984
  · exact checkSingleBlackFast_sound sbCell0985
  · exact checkSingleBlackFast_sound sbCell0986
  · exact checkSingleBlackFast_sound sbCell0987
  · exact checkSingleBlackFast_sound sbCell0988
  · exact checkSingleBlackFast_sound sbCell0989
  · exact checkSingleBlackFast_sound sbCell0990
  · exact checkSingleBlackFast_sound sbCell0991
  · exact checkSingleBlackFast_sound sbCell0992
  · exact checkSingleBlackFast_sound sbCell0993
  · exact checkSingleBlackFast_sound sbCell0994
  · exact checkSingleBlackFast_sound sbCell0995
  · exact checkSingleBlackFast_sound sbCell0996
  · exact checkSingleBlackFast2_sound sbCell0997
  · exact checkSingleBlack_sound sbCell0998

end LangtonsAnt
