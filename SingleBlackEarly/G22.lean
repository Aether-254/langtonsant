import FastCell2
import SingleBlackEarly.C0814
import SingleBlackEarly.C0815
import SingleBlackEarly.C0816
import SingleBlackEarly.C0817
import SingleBlackEarly.C0818
import SingleBlackEarly.C0819
import SingleBlackEarly.C0820
import SingleBlackEarly.C0821
import SingleBlackEarly.C0822
import SingleBlackEarly.C0823
import SingleBlackEarly.C0824
import SingleBlackEarly.C0825
import SingleBlackEarly.C0826
import SingleBlackEarly.C0827
import SingleBlackEarly.C0828
import SingleBlackEarly.C0829
import SingleBlackEarly.C0830
import SingleBlackEarly.C0831
import SingleBlackEarly.C0832
import SingleBlackEarly.C0833
import SingleBlackEarly.C0834
import SingleBlackEarly.C0835
import SingleBlackEarly.C0836
import SingleBlackEarly.C0837
import SingleBlackEarly.C0838
import SingleBlackEarly.C0839
import SingleBlackEarly.C0840
import SingleBlackEarly.C0841
import SingleBlackEarly.C0842
import SingleBlackEarly.C0843
import SingleBlackEarly.C0844
import SingleBlackEarly.C0845
import SingleBlackEarly.C0846
import SingleBlackEarly.C0847
import SingleBlackEarly.C0848
import SingleBlackEarly.C0849
import SingleBlackEarly.C0850

namespace LangtonsAnt

def sbGroup22 : List Point :=
  [(26, -4), (24, -3), (24, -2), (25, -2), (23, -2), (23, -1), (24, -1), (23, -3), (22, -3), (22, -2), (21, -2), (22, -1), (21, 1), (22, 1), (22, 0), (22, 2), (23, 2), (23, 1), (21, 2), (21, 3), (22, 3), (20, 3), (4, 16), (5, 16), (0, 13), (-2, 15), (-2, 16), (-1, 16), (-2, 14), (-3, 15), (-5, 10), (-4, 8), (-5, 9), (-7, 8), (-7, 9), (-6, 9), (-8, 9)]

theorem sbGroup22_ok : forall q, q ∈ sbGroup22 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup22, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0814
  · exact checkSingleBlackFast_sound sbCell0815
  · exact checkSingleBlackFast_sound sbCell0816
  · exact checkSingleBlackFast2_sound sbCell0817
  · exact checkSingleBlackFast2_sound sbCell0818
  · exact checkSingleBlackFast_sound sbCell0819
  · exact checkSingleBlack_sound sbCell0820
  · exact checkSingleBlackFast_sound sbCell0821
  · exact checkSingleBlackFast2_sound sbCell0822
  · exact checkSingleBlackFast_sound sbCell0823
  · exact checkSingleBlack_sound sbCell0824
  · exact checkSingleBlack_sound sbCell0825
  · exact checkSingleBlackFast2_sound sbCell0826
  · exact checkSingleBlackFast_sound sbCell0827
  · exact checkSingleBlackFast_sound sbCell0828
  · exact checkSingleBlackFast_sound sbCell0829
  · exact checkSingleBlackFast2_sound sbCell0830
  · exact checkSingleBlackFast_sound sbCell0831
  · exact checkSingleBlackFast2_sound sbCell0832
  · exact checkSingleBlackFast_sound sbCell0833
  · exact checkSingleBlackFast2_sound sbCell0834
  · exact checkSingleBlackFast_sound sbCell0835
  · exact checkSingleBlackFast_sound sbCell0836
  · exact checkSingleBlackFast2_sound sbCell0837
  · exact checkSingleBlack_sound sbCell0838
  · exact checkSingleBlackFast_sound sbCell0839
  · exact checkSingleBlack_sound sbCell0840
  · exact checkSingleBlackFast_sound sbCell0841
  · exact checkSingleBlackFast2_sound sbCell0842
  · exact checkSingleBlackFast_sound sbCell0843
  · exact checkSingleBlackFast2_sound sbCell0844
  · exact checkSingleBlackFast_sound sbCell0845
  · exact checkSingleBlackFast2_sound sbCell0846
  · exact checkSingleBlackFast_sound sbCell0847
  · exact checkSingleBlackFast_sound sbCell0848
  · exact checkSingleBlackFast_sound sbCell0849
  · exact checkSingleBlackFast_sound sbCell0850

end LangtonsAnt
