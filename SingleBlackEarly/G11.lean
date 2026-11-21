import FastCell2
import SingleBlackEarly.C0407
import SingleBlackEarly.C0408
import SingleBlackEarly.C0409
import SingleBlackEarly.C0410
import SingleBlackEarly.C0411
import SingleBlackEarly.C0412
import SingleBlackEarly.C0413
import SingleBlackEarly.C0414
import SingleBlackEarly.C0415
import SingleBlackEarly.C0416
import SingleBlackEarly.C0417
import SingleBlackEarly.C0418
import SingleBlackEarly.C0419
import SingleBlackEarly.C0420
import SingleBlackEarly.C0421
import SingleBlackEarly.C0422
import SingleBlackEarly.C0423
import SingleBlackEarly.C0424
import SingleBlackEarly.C0425
import SingleBlackEarly.C0426
import SingleBlackEarly.C0427
import SingleBlackEarly.C0428
import SingleBlackEarly.C0429
import SingleBlackEarly.C0430
import SingleBlackEarly.C0431
import SingleBlackEarly.C0432
import SingleBlackEarly.C0433
import SingleBlackEarly.C0434
import SingleBlackEarly.C0435
import SingleBlackEarly.C0436
import SingleBlackEarly.C0437
import SingleBlackEarly.C0438
import SingleBlackEarly.C0439
import SingleBlackEarly.C0440
import SingleBlackEarly.C0441
import SingleBlackEarly.C0442
import SingleBlackEarly.C0443

namespace LangtonsAnt

def sbGroup11 : List Point :=
  [(14, -7), (15, -5), (16, -5), (16, -6), (16, -4), (17, -4), (17, -5), (15, -4), (16, -3), (16, 0), (17, 0), (17, -1), (15, 0), (16, 1), (17, 1), (18, 1), (18, 0), (18, 2), (19, 2), (19, 1), (17, 2), (17, 3), (18, 3), (18, 4), (19, 4), (19, 3), (17, 4), (17, 5), (18, 5), (16, 5), (16, 6), (17, 6), (16, 4), (15, 4), (15, 5), (15, 6), (16, 7)]

theorem sbGroup11_ok : forall q, q ∈ sbGroup11 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup11, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0407
  · exact checkSingleBlackFast_sound sbCell0408
  · exact checkSingleBlackFast_sound sbCell0409
  · exact checkSingleBlackFast_sound sbCell0410
  · exact checkSingleBlackFast2_sound sbCell0411
  · exact checkSingleBlackFast_sound sbCell0412
  · exact checkSingleBlackFast_sound sbCell0413
  · exact checkSingleBlackFast_sound sbCell0414
  · exact checkSingleBlackFast_sound sbCell0415
  · exact checkSingleBlackFast_sound sbCell0416
  · exact checkSingleBlackFast_sound sbCell0417
  · exact checkSingleBlackFast2_sound sbCell0418
  · exact checkSingleBlackFast_sound sbCell0419
  · exact checkSingleBlackFast_sound sbCell0420
  · exact checkSingleBlackFast_sound sbCell0421
  · exact checkSingleBlackFast_sound sbCell0422
  · exact checkSingleBlackFast_sound sbCell0423
  · exact checkSingleBlackFast_sound sbCell0424
  · exact checkSingleBlackFast_sound sbCell0425
  · exact checkSingleBlackFast_sound sbCell0426
  · exact checkSingleBlackFast_sound sbCell0427
  · exact checkSingleBlackFast_sound sbCell0428
  · exact checkSingleBlackFast_sound sbCell0429
  · exact checkSingleBlackFast_sound sbCell0430
  · exact checkSingleBlackFast_sound sbCell0431
  · exact checkSingleBlackFast_sound sbCell0432
  · exact checkSingleBlackFast_sound sbCell0433
  · exact checkSingleBlack_sound sbCell0434
  · exact checkSingleBlackFast2_sound sbCell0435
  · exact checkSingleBlackFast_sound sbCell0436
  · exact checkSingleBlackFast_sound sbCell0437
  · exact checkSingleBlackFast_sound sbCell0438
  · exact checkSingleBlackFast_sound sbCell0439
  · exact checkSingleBlackFast_sound sbCell0440
  · exact checkSingleBlackFast_sound sbCell0441
  · exact checkSingleBlackFast_sound sbCell0442
  · exact checkSingleBlackFast_sound sbCell0443

end LangtonsAnt
