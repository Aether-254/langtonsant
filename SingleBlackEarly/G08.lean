import FastCell2
import SingleBlackEarly.C0296
import SingleBlackEarly.C0297
import SingleBlackEarly.C0298
import SingleBlackEarly.C0299
import SingleBlackEarly.C0300
import SingleBlackEarly.C0301
import SingleBlackEarly.C0302
import SingleBlackEarly.C0303
import SingleBlackEarly.C0304
import SingleBlackEarly.C0305
import SingleBlackEarly.C0306
import SingleBlackEarly.C0307
import SingleBlackEarly.C0308
import SingleBlackEarly.C0309
import SingleBlackEarly.C0310
import SingleBlackEarly.C0311
import SingleBlackEarly.C0312
import SingleBlackEarly.C0313
import SingleBlackEarly.C0314
import SingleBlackEarly.C0315
import SingleBlackEarly.C0316
import SingleBlackEarly.C0317
import SingleBlackEarly.C0318
import SingleBlackEarly.C0319
import SingleBlackEarly.C0320
import SingleBlackEarly.C0321
import SingleBlackEarly.C0322
import SingleBlackEarly.C0323
import SingleBlackEarly.C0324
import SingleBlackEarly.C0325
import SingleBlackEarly.C0326
import SingleBlackEarly.C0327
import SingleBlackEarly.C0328
import SingleBlackEarly.C0329
import SingleBlackEarly.C0330
import SingleBlackEarly.C0331
import SingleBlackEarly.C0332

namespace LangtonsAnt

def sbGroup08 : List Point :=
  [(9, 11), (8, 11), (8, 12), (7, 12), (7, 13), (8, 13), (7, 11), (6, 11), (6, 12), (5, 12), (5, 13), (6, 13), (5, 11), (4, 11), (4, 12), (4, 10), (3, 11), (1, 10), (1, 11), (2, 11), (0, 11), (0, 12), (1, 12), (0, 10), (-1, 10), (-1, 11), (-2, 11), (-2, 12), (-1, 12), (-2, 10), (-3, 10), (-3, 11), (-3, 9), (-4, 9), (-4, 10), (-2, 9), (3, 12)]

theorem sbGroup08_ok : forall q, q ∈ sbGroup08 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup08, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0296
  · exact checkSingleBlackFast2_sound sbCell0297
  · exact checkSingleBlackFast_sound sbCell0298
  · exact checkSingleBlackFast_sound sbCell0299
  · exact checkSingleBlackFast_sound sbCell0300
  · exact checkSingleBlackFast_sound sbCell0301
  · exact checkSingleBlackFast_sound sbCell0302
  · exact checkSingleBlackFast_sound sbCell0303
  · exact checkSingleBlackFast_sound sbCell0304
  · exact checkSingleBlackFast2_sound sbCell0305
  · exact checkSingleBlackFast_sound sbCell0306
  · exact checkSingleBlackFast_sound sbCell0307
  · exact checkSingleBlackFast_sound sbCell0308
  · exact checkSingleBlackFast_sound sbCell0309
  · exact checkSingleBlackFast_sound sbCell0310
  · exact checkSingleBlackFast_sound sbCell0311
  · exact checkSingleBlackFast_sound sbCell0312
  · exact checkSingleBlackFast_sound sbCell0313
  · exact checkSingleBlackFast_sound sbCell0314
  · exact checkSingleBlackFast_sound sbCell0315
  · exact checkSingleBlack_sound sbCell0316
  · exact checkSingleBlackFast_sound sbCell0317
  · exact checkSingleBlackFast_sound sbCell0318
  · exact checkSingleBlackFast_sound sbCell0319
  · exact checkSingleBlackFast_sound sbCell0320
  · exact checkSingleBlackFast_sound sbCell0321
  · exact checkSingleBlackFast_sound sbCell0322
  · exact checkSingleBlackFast_sound sbCell0323
  · exact checkSingleBlackFast_sound sbCell0324
  · exact checkSingleBlackFast_sound sbCell0325
  · exact checkSingleBlackFast_sound sbCell0326
  · exact checkSingleBlackFast_sound sbCell0327
  · exact checkSingleBlackFast_sound sbCell0328
  · exact checkSingleBlackFast_sound sbCell0329
  · exact checkSingleBlackFast_sound sbCell0330
  · exact checkSingleBlackFast_sound sbCell0331
  · exact checkSingleBlackFast_sound sbCell0332

end LangtonsAnt
