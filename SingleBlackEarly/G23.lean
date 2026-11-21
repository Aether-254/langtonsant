import FastCell2
import SegmentCheck
import SingleBlackEarly.C0851
import SingleBlackEarly.C0852
import SingleBlackEarly.C0853
import SingleBlackEarly.C0854
import SingleBlackEarly.C0855
import SingleBlackEarly.C0856
import SingleBlackEarly.C0857
import SingleBlackEarly.C0858
import SingleBlackEarly.C0859
import SingleBlackEarly.C0860
import SingleBlackEarly.C0861
import SingleBlackEarly.C0862
import SingleBlackEarly.C0863
import SingleBlackEarly.C0864
import SingleBlackEarly.C0865
import SingleBlackEarly.C0866
import SingleBlackEarly.C0867
import SingleBlackEarly.C0868
import SingleBlackEarly.C0869
import SingleBlackEarly.C0870
import SingleBlackEarly.C0871
import SingleBlackEarly.C0872
import SingleBlackEarly.C0873
import SingleBlackEarly.C0874
import SingleBlackEarly.C0875
import SingleBlackEarly.C0876
import SingleBlackEarly.C0877
import SingleBlackEarly.C0878
import SingleBlackEarly.C0879
import SingleBlackEarly.C0880
import SingleBlackEarly.C0881
import SingleBlackEarly.C0882
import SingleBlackEarly.C0883
import SingleBlackEarly.C0884
import SingleBlackEarly.C0885
import SingleBlackEarly.C0886
import SingleBlackEarly.C0887

namespace LangtonsAnt

def sbGroup23 : List Point :=
  [(-8, 10), (-7, 10), (-8, 8), (-9, 8), (-9, 9), (-9, 7), (-10, 7), (-10, 8), (-8, 7), (-9, 6), (-7, 3), (-8, 3), (-8, 4), (-8, 2), (-9, 2), (-9, 3), (-7, 2), (-8, 1), (-7, -1), (-8, -1), (-8, 0), (-6, -1), (-9, 1), (-10, 1), (-10, 2), (-10, 0), (-11, 0), (-11, 1), (-9, 0), (-9, -1), (-10, -1), (-10, -2), (-11, -2), (-11, -1), (-9, -2), (-9, -3), (-10, -3)]

theorem sbGroup23_ok : forall q, q ∈ sbGroup23 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup23, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0851
  · exact checkSingleBlackFast_sound sbCell0852
  · exact checkSingleBlackFast_sound sbCell0853
  · exact checkSingleBlackFast_sound sbCell0854
  · exact checkSingleBlack_sound sbCell0855
  · exact checkSingleBlackFast_sound sbCell0856
  · exact checkSingleBlackFast_sound sbCell0857
  · exact checkSingleBlackFast2_sound sbCell0858
  · exact checkSingleBlackFast_sound sbCell0859
  · exact checkSingleBlack_sound sbCell0860
  · exact checkSingleBlackFast_sound sbCell0861
  · exact checkSingleBlackFast2_sound sbCell0862
  · exact checkSingleBlackFast_sound sbCell0863
  · exact checkSingleBlackFast2_sound sbCell0864
  · exact checkSingleBlackFast2_sound sbCell0865
  · exact checkSingleBlackFast2_sound sbCell0866
  · exact checkSingleBlackFast_sound sbCell0867
  · exact checkSingleBlackFast_sound sbCell0868
  · exact checkSingleBlackFast_sound sbCell0869
  · exact checkSingleBlack_sound sbCell0870
  · exact checkSingleBlackFast_sound sbCell0871
  · exact checkSingleBlack_sound sbCell0872
  · exact sbCell0873
  · exact checkSingleBlackFast_sound sbCell0874
  · exact checkSingleBlackFast_sound sbCell0875
  · exact checkSingleBlackFast_sound sbCell0876
  · exact checkSingleBlackFast2_sound sbCell0877
  · exact checkSingleBlackFast2_sound sbCell0878
  · exact checkSingleBlackFast2_sound sbCell0879
  · exact checkSingleBlackFast_sound sbCell0880
  · exact checkSingleBlackFast_sound sbCell0881
  · exact checkSingleBlack_sound sbCell0882
  · exact checkSingleBlackFast_sound sbCell0883
  · exact checkSingleBlackFast_sound sbCell0884
  · exact checkSingleBlackFast_sound sbCell0885
  · exact checkSingleBlackFast2_sound sbCell0886
  · exact checkSingleBlackFast_sound sbCell0887

end LangtonsAnt
