import FastCell2
import SegmentCheck
import SingleBlackEarly.C0222
import SingleBlackEarly.C0223
import SingleBlackEarly.C0224
import SingleBlackEarly.C0225
import SingleBlackEarly.C0226
import SingleBlackEarly.C0227
import SingleBlackEarly.C0228
import SingleBlackEarly.C0229
import SingleBlackEarly.C0230
import SingleBlackEarly.C0231
import SingleBlackEarly.C0232
import SingleBlackEarly.C0233
import SingleBlackEarly.C0234
import SingleBlackEarly.C0235
import SingleBlackEarly.C0236
import SingleBlackEarly.C0237
import SingleBlackEarly.C0238
import SingleBlackEarly.C0239
import SingleBlackEarly.C0240
import SingleBlackEarly.C0241
import SingleBlackEarly.C0242
import SingleBlackEarly.C0243
import SingleBlackEarly.C0244
import SingleBlackEarly.C0245
import SingleBlackEarly.C0246
import SingleBlackEarly.C0247
import SingleBlackEarly.C0248
import SingleBlackEarly.C0249
import SingleBlackEarly.C0250
import SingleBlackEarly.C0251
import SingleBlackEarly.C0252
import SingleBlackEarly.C0253
import SingleBlackEarly.C0254
import SingleBlackEarly.C0255
import SingleBlackEarly.C0256
import SingleBlackEarly.C0257
import SingleBlackEarly.C0258

namespace LangtonsAnt

def sbGroup06 : List Point :=
  [(10, 9), (8, 9), (8, 10), (9, 10), (8, 8), (7, 8), (7, 9), (6, 9), (6, 10), (7, 10), (6, 8), (5, 9), (3, 8), (3, 9), (4, 9), (2, 9), (2, 10), (3, 10), (2, 8), (1, 9), (-5, -2), (-5, -1), (-1, -5), (11, 5), (12, 5), (12, 4), (12, 6), (13, 6), (13, 5), (11, 6), (11, 9), (12, 9), (12, 8), (12, 10), (13, 10), (13, 9), (11, 10)]

theorem sbGroup06_ok : forall q, q ∈ sbGroup06 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup06, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0222
  · exact checkSingleBlackFast_sound sbCell0223
  · exact checkSingleBlackFast_sound sbCell0224
  · exact checkSingleBlackFast_sound sbCell0225
  · exact checkSingleBlackFast_sound sbCell0226
  · exact sbCell0227
  · exact checkSingleBlackFast_sound sbCell0228
  · exact checkSingleBlackFast_sound sbCell0229
  · exact checkSingleBlackFast_sound sbCell0230
  · exact checkSingleBlackFast_sound sbCell0231
  · exact checkSingleBlackFast2_sound sbCell0232
  · exact checkSingleBlackFast_sound sbCell0233
  · exact checkSingleBlackFast2_sound sbCell0234
  · exact checkSingleBlackFast_sound sbCell0235
  · exact checkSingleBlackFast_sound sbCell0236
  · exact checkSingleBlackFast_sound sbCell0237
  · exact checkSingleBlackFast_sound sbCell0238
  · exact checkSingleBlackFast_sound sbCell0239
  · exact checkSingleBlackFast_sound sbCell0240
  · exact checkSingleBlackFast_sound sbCell0241
  · exact checkSingleBlackFast2_sound sbCell0242
  · exact checkSingleBlackFast_sound sbCell0243
  · exact checkSingleBlackFast_sound sbCell0244
  · exact checkSingleBlackFast_sound sbCell0245
  · exact checkSingleBlackFast_sound sbCell0246
  · exact checkSingleBlackFast_sound sbCell0247
  · exact checkSingleBlackFast_sound sbCell0248
  · exact checkSingleBlackFast_sound sbCell0249
  · exact checkSingleBlackFast_sound sbCell0250
  · exact checkSingleBlackFast_sound sbCell0251
  · exact checkSingleBlackFast_sound sbCell0252
  · exact checkSingleBlackFast_sound sbCell0253
  · exact checkSingleBlackFast_sound sbCell0254
  · exact checkSingleBlackFast_sound sbCell0255
  · exact checkSingleBlackFast2_sound sbCell0256
  · exact checkSingleBlackFast_sound sbCell0257
  · exact checkSingleBlackFast_sound sbCell0258

end LangtonsAnt
