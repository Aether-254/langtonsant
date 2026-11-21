import FastCell2
import SingleBlackEarly.C0333
import SingleBlackEarly.C0334
import SingleBlackEarly.C0335
import SingleBlackEarly.C0336
import SingleBlackEarly.C0337
import SingleBlackEarly.C0338
import SingleBlackEarly.C0339
import SingleBlackEarly.C0340
import SingleBlackEarly.C0341
import SingleBlackEarly.C0342
import SingleBlackEarly.C0343
import SingleBlackEarly.C0344
import SingleBlackEarly.C0345
import SingleBlackEarly.C0346
import SingleBlackEarly.C0347
import SingleBlackEarly.C0348
import SingleBlackEarly.C0349
import SingleBlackEarly.C0350
import SingleBlackEarly.C0351
import SingleBlackEarly.C0352
import SingleBlackEarly.C0353
import SingleBlackEarly.C0354
import SingleBlackEarly.C0355
import SingleBlackEarly.C0356
import SingleBlackEarly.C0357
import SingleBlackEarly.C0358
import SingleBlackEarly.C0359
import SingleBlackEarly.C0360
import SingleBlackEarly.C0361
import SingleBlackEarly.C0362
import SingleBlackEarly.C0363
import SingleBlackEarly.C0364
import SingleBlackEarly.C0365
import SingleBlackEarly.C0366
import SingleBlackEarly.C0367
import SingleBlackEarly.C0368
import SingleBlackEarly.C0369

namespace LangtonsAnt

def sbGroup09 : List Point :=
  [(3, 13), (4, 13), (2, 13), (2, 14), (3, 14), (2, 12), (1, 13), (-3, 12), (-3, 13), (-2, 13), (-4, 13), (-4, 14), (-3, 14), (-4, 12), (-5, 12), (-5, 13), (-5, 11), (-6, 11), (-6, 12), (-4, 11), (-3, 8), (-1, 6), (-7, 4), (12, -1), (12, -2), (11, -2), (12, 0), (13, 0), (13, -1), (13, 1), (14, 1), (14, 0), (12, 1), (12, 2), (13, 2), (12, 3), (13, -2)]

theorem sbGroup09_ok : forall q, q ∈ sbGroup09 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup09, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0333
  · exact checkSingleBlackFast_sound sbCell0334
  · exact checkSingleBlackFast_sound sbCell0335
  · exact checkSingleBlackFast_sound sbCell0336
  · exact checkSingleBlackFast_sound sbCell0337
  · exact checkSingleBlackFast_sound sbCell0338
  · exact checkSingleBlackFast_sound sbCell0339
  · exact checkSingleBlackFast_sound sbCell0340
  · exact checkSingleBlackFast_sound sbCell0341
  · exact checkSingleBlackFast_sound sbCell0342
  · exact checkSingleBlackFast_sound sbCell0343
  · exact checkSingleBlackFast_sound sbCell0344
  · exact checkSingleBlackFast_sound sbCell0345
  · exact checkSingleBlackFast2_sound sbCell0346
  · exact checkSingleBlackFast2_sound sbCell0347
  · exact checkSingleBlackFast_sound sbCell0348
  · exact checkSingleBlackFast_sound sbCell0349
  · exact checkSingleBlackFast_sound sbCell0350
  · exact checkSingleBlackFast_sound sbCell0351
  · exact checkSingleBlackFast_sound sbCell0352
  · exact checkSingleBlackFast_sound sbCell0353
  · exact checkSingleBlackFast_sound sbCell0354
  · exact checkSingleBlackFast_sound sbCell0355
  · exact checkSingleBlackFast_sound sbCell0356
  · exact checkSingleBlackFast2_sound sbCell0357
  · exact checkSingleBlackFast_sound sbCell0358
  · exact checkSingleBlackFast_sound sbCell0359
  · exact checkSingleBlackFast_sound sbCell0360
  · exact checkSingleBlackFast_sound sbCell0361
  · exact checkSingleBlackFast_sound sbCell0362
  · exact checkSingleBlackFast_sound sbCell0363
  · exact checkSingleBlackFast_sound sbCell0364
  · exact checkSingleBlackFast_sound sbCell0365
  · exact checkSingleBlackFast_sound sbCell0366
  · exact checkSingleBlackFast_sound sbCell0367
  · exact checkSingleBlackFast_sound sbCell0368
  · exact checkSingleBlackFast_sound sbCell0369

end LangtonsAnt
