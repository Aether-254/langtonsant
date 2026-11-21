import FastCell2
import SingleBlackEarly.C0185
import SingleBlackEarly.C0186
import SingleBlackEarly.C0187
import SingleBlackEarly.C0188
import SingleBlackEarly.C0189
import SingleBlackEarly.C0190
import SingleBlackEarly.C0191
import SingleBlackEarly.C0192
import SingleBlackEarly.C0193
import SingleBlackEarly.C0194
import SingleBlackEarly.C0195
import SingleBlackEarly.C0196
import SingleBlackEarly.C0197
import SingleBlackEarly.C0198
import SingleBlackEarly.C0199
import SingleBlackEarly.C0200
import SingleBlackEarly.C0201
import SingleBlackEarly.C0202
import SingleBlackEarly.C0203
import SingleBlackEarly.C0204
import SingleBlackEarly.C0205
import SingleBlackEarly.C0206
import SingleBlackEarly.C0207
import SingleBlackEarly.C0208
import SingleBlackEarly.C0209
import SingleBlackEarly.C0210
import SingleBlackEarly.C0211
import SingleBlackEarly.C0212
import SingleBlackEarly.C0213
import SingleBlackEarly.C0214
import SingleBlackEarly.C0215
import SingleBlackEarly.C0216
import SingleBlackEarly.C0217
import SingleBlackEarly.C0218
import SingleBlackEarly.C0219
import SingleBlackEarly.C0220
import SingleBlackEarly.C0221

namespace LangtonsAnt

def sbGroup05 : List Point :=
  [(8, -3), (9, -1), (10, -1), (10, -2), (10, 0), (11, 0), (11, -1), (9, 0), (9, 1), (10, 1), (10, 2), (11, 2), (11, 1), (9, 2), (9, 3), (10, 3), (10, 4), (11, 4), (11, 3), (9, 4), (9, 5), (10, 5), (8, 5), (8, 6), (9, 6), (8, 4), (7, 4), (7, 7), (8, 7), (9, 7), (10, 7), (10, 6), (10, 8), (11, 8), (11, 7), (9, 8), (9, 9)]

theorem sbGroup05_ok : forall q, q ∈ sbGroup05 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup05, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0185
  · exact checkSingleBlackFast_sound sbCell0186
  · exact checkSingleBlackFast_sound sbCell0187
  · exact checkSingleBlackFast_sound sbCell0188
  · exact checkSingleBlackFast_sound sbCell0189
  · exact checkSingleBlackFast_sound sbCell0190
  · exact checkSingleBlackFast_sound sbCell0191
  · exact checkSingleBlackFast_sound sbCell0192
  · exact checkSingleBlackFast_sound sbCell0193
  · exact checkSingleBlackFast_sound sbCell0194
  · exact checkSingleBlackFast_sound sbCell0195
  · exact checkSingleBlackFast2_sound sbCell0196
  · exact checkSingleBlackFast_sound sbCell0197
  · exact checkSingleBlackFast_sound sbCell0198
  · exact checkSingleBlackFast_sound sbCell0199
  · exact checkSingleBlackFast2_sound sbCell0200
  · exact checkSingleBlackFast_sound sbCell0201
  · exact checkSingleBlackFast_sound sbCell0202
  · exact checkSingleBlackFast_sound sbCell0203
  · exact checkSingleBlackFast_sound sbCell0204
  · exact checkSingleBlackFast_sound sbCell0205
  · exact checkSingleBlackFast_sound sbCell0206
  · exact checkSingleBlackFast_sound sbCell0207
  · exact checkSingleBlackFast_sound sbCell0208
  · exact checkSingleBlackFast_sound sbCell0209
  · exact checkSingleBlackFast_sound sbCell0210
  · exact checkSingleBlackFast_sound sbCell0211
  · exact checkSingleBlack_sound sbCell0212
  · exact checkSingleBlackFast_sound sbCell0213
  · exact checkSingleBlackFast_sound sbCell0214
  · exact checkSingleBlackFast_sound sbCell0215
  · exact checkSingleBlackFast_sound sbCell0216
  · exact checkSingleBlackFast_sound sbCell0217
  · exact checkSingleBlackFast_sound sbCell0218
  · exact checkSingleBlackFast_sound sbCell0219
  · exact checkSingleBlackFast_sound sbCell0220
  · exact checkSingleBlackFast2_sound sbCell0221

end LangtonsAnt
