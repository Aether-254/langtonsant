import FastCell2
import SingleBlackEarly.C0444
import SingleBlackEarly.C0445
import SingleBlackEarly.C0446
import SingleBlackEarly.C0447
import SingleBlackEarly.C0448
import SingleBlackEarly.C0449
import SingleBlackEarly.C0450
import SingleBlackEarly.C0451
import SingleBlackEarly.C0452
import SingleBlackEarly.C0453
import SingleBlackEarly.C0454
import SingleBlackEarly.C0455
import SingleBlackEarly.C0456
import SingleBlackEarly.C0457
import SingleBlackEarly.C0458
import SingleBlackEarly.C0459
import SingleBlackEarly.C0460
import SingleBlackEarly.C0461
import SingleBlackEarly.C0462
import SingleBlackEarly.C0463
import SingleBlackEarly.C0464
import SingleBlackEarly.C0465
import SingleBlackEarly.C0466
import SingleBlackEarly.C0467
import SingleBlackEarly.C0468
import SingleBlackEarly.C0469
import SingleBlackEarly.C0470
import SingleBlackEarly.C0471
import SingleBlackEarly.C0472
import SingleBlackEarly.C0473
import SingleBlackEarly.C0474
import SingleBlackEarly.C0475
import SingleBlackEarly.C0476
import SingleBlackEarly.C0477
import SingleBlackEarly.C0478
import SingleBlackEarly.C0479
import SingleBlackEarly.C0480

namespace LangtonsAnt

def sbGroup12 : List Point :=
  [(17, 7), (18, 7), (18, 6), (18, 8), (19, 8), (19, 7), (17, 8), (17, 9), (18, 9), (18, 10), (19, 10), (19, 9), (17, 10), (17, 11), (18, 11), (18, 12), (19, 12), (19, 11), (17, 12), (17, 13), (18, 13), (16, 13), (16, 14), (17, 14), (16, 12), (12, 13), (12, 14), (13, 14), (11, 14), (11, 15), (12, 15), (11, 13), (10, 14), (5, 10), (-3, 7), (9, 14), (9, 15)]

theorem sbGroup12_ok : forall q, q ∈ sbGroup12 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup12, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0444
  · exact checkSingleBlackFast_sound sbCell0445
  · exact checkSingleBlackFast_sound sbCell0446
  · exact checkSingleBlackFast_sound sbCell0447
  · exact checkSingleBlackFast_sound sbCell0448
  · exact checkSingleBlackFast_sound sbCell0449
  · exact checkSingleBlackFast_sound sbCell0450
  · exact checkSingleBlackFast_sound sbCell0451
  · exact checkSingleBlackFast2_sound sbCell0452
  · exact checkSingleBlackFast_sound sbCell0453
  · exact checkSingleBlack_sound sbCell0454
  · exact checkSingleBlackFast_sound sbCell0455
  · exact checkSingleBlackFast_sound sbCell0456
  · exact checkSingleBlackFast_sound sbCell0457
  · exact checkSingleBlackFast_sound sbCell0458
  · exact checkSingleBlackFast_sound sbCell0459
  · exact checkSingleBlackFast_sound sbCell0460
  · exact checkSingleBlackFast_sound sbCell0461
  · exact checkSingleBlackFast_sound sbCell0462
  · exact checkSingleBlackFast_sound sbCell0463
  · exact checkSingleBlack_sound sbCell0464
  · exact checkSingleBlackFast_sound sbCell0465
  · exact checkSingleBlackFast2_sound sbCell0466
  · exact checkSingleBlackFast_sound sbCell0467
  · exact checkSingleBlackFast_sound sbCell0468
  · exact checkSingleBlackFast_sound sbCell0469
  · exact checkSingleBlackFast2_sound sbCell0470
  · exact checkSingleBlackFast_sound sbCell0471
  · exact checkSingleBlackFast_sound sbCell0472
  · exact checkSingleBlackFast_sound sbCell0473
  · exact checkSingleBlackFast2_sound sbCell0474
  · exact checkSingleBlackFast2_sound sbCell0475
  · exact checkSingleBlackFast_sound sbCell0476
  · exact checkSingleBlackFast_sound sbCell0477
  · exact checkSingleBlackFast_sound sbCell0478
  · exact checkSingleBlackFast_sound sbCell0479
  · exact checkSingleBlackFast_sound sbCell0480

end LangtonsAnt
