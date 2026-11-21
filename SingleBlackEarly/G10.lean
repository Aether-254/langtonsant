import FastCell2
import SingleBlackEarly.C0370
import SingleBlackEarly.C0371
import SingleBlackEarly.C0372
import SingleBlackEarly.C0373
import SingleBlackEarly.C0374
import SingleBlackEarly.C0375
import SingleBlackEarly.C0376
import SingleBlackEarly.C0377
import SingleBlackEarly.C0378
import SingleBlackEarly.C0379
import SingleBlackEarly.C0380
import SingleBlackEarly.C0381
import SingleBlackEarly.C0382
import SingleBlackEarly.C0383
import SingleBlackEarly.C0384
import SingleBlackEarly.C0385
import SingleBlackEarly.C0386
import SingleBlackEarly.C0387
import SingleBlackEarly.C0388
import SingleBlackEarly.C0389
import SingleBlackEarly.C0390
import SingleBlackEarly.C0391
import SingleBlackEarly.C0392
import SingleBlackEarly.C0393
import SingleBlackEarly.C0394
import SingleBlackEarly.C0395
import SingleBlackEarly.C0396
import SingleBlackEarly.C0397
import SingleBlackEarly.C0398
import SingleBlackEarly.C0399
import SingleBlackEarly.C0400
import SingleBlackEarly.C0401
import SingleBlackEarly.C0402
import SingleBlackEarly.C0403
import SingleBlackEarly.C0404
import SingleBlackEarly.C0405
import SingleBlackEarly.C0406

namespace LangtonsAnt

def sbGroup10 : List Point :=
  [(13, -3), (12, -3), (14, -3), (14, -4), (13, -4), (14, -2), (15, -2), (15, -3), (15, -1), (16, -1), (16, -2), (14, -1), (14, 2), (15, 2), (15, 1), (15, 3), (16, 3), (16, 2), (14, 3), (13, 3), (12, -4), (11, -4), (11, -3), (11, -5), (10, -5), (10, -4), (12, -5), (12, -6), (11, -6), (13, -6), (13, -7), (12, -7), (13, -5), (14, -5), (14, -6), (15, -6), (15, -7)]

theorem sbGroup10_ok : forall q, q ∈ sbGroup10 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup10, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0370
  · exact checkSingleBlackFast_sound sbCell0371
  · exact checkSingleBlackFast_sound sbCell0372
  · exact checkSingleBlackFast_sound sbCell0373
  · exact checkSingleBlackFast_sound sbCell0374
  · exact checkSingleBlackFast2_sound sbCell0375
  · exact checkSingleBlackFast_sound sbCell0376
  · exact checkSingleBlackFast_sound sbCell0377
  · exact checkSingleBlackFast2_sound sbCell0378
  · exact checkSingleBlackFast_sound sbCell0379
  · exact checkSingleBlackFast_sound sbCell0380
  · exact checkSingleBlackFast_sound sbCell0381
  · exact checkSingleBlackFast_sound sbCell0382
  · exact checkSingleBlackFast_sound sbCell0383
  · exact checkSingleBlackFast_sound sbCell0384
  · exact checkSingleBlackFast_sound sbCell0385
  · exact checkSingleBlackFast_sound sbCell0386
  · exact checkSingleBlackFast_sound sbCell0387
  · exact checkSingleBlackFast_sound sbCell0388
  · exact checkSingleBlackFast_sound sbCell0389
  · exact checkSingleBlackFast_sound sbCell0390
  · exact checkSingleBlackFast_sound sbCell0391
  · exact checkSingleBlackFast_sound sbCell0392
  · exact checkSingleBlackFast_sound sbCell0393
  · exact checkSingleBlackFast_sound sbCell0394
  · exact checkSingleBlackFast_sound sbCell0395
  · exact checkSingleBlackFast2_sound sbCell0396
  · exact checkSingleBlackFast_sound sbCell0397
  · exact checkSingleBlackFast_sound sbCell0398
  · exact checkSingleBlackFast_sound sbCell0399
  · exact checkSingleBlackFast_sound sbCell0400
  · exact checkSingleBlackFast_sound sbCell0401
  · exact checkSingleBlackFast_sound sbCell0402
  · exact checkSingleBlack_sound sbCell0403
  · exact checkSingleBlackFast_sound sbCell0404
  · exact checkSingleBlackFast_sound sbCell0405
  · exact checkSingleBlackFast_sound sbCell0406

end LangtonsAnt
