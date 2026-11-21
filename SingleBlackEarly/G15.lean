import FastCell2
import SingleBlackEarly.C0555
import SingleBlackEarly.C0556
import SingleBlackEarly.C0557
import SingleBlackEarly.C0558
import SingleBlackEarly.C0559
import SingleBlackEarly.C0560
import SingleBlackEarly.C0561
import SingleBlackEarly.C0562
import SingleBlackEarly.C0563
import SingleBlackEarly.C0564
import SingleBlackEarly.C0565
import SingleBlackEarly.C0566
import SingleBlackEarly.C0567
import SingleBlackEarly.C0568
import SingleBlackEarly.C0569
import SingleBlackEarly.C0570
import SingleBlackEarly.C0571
import SingleBlackEarly.C0572
import SingleBlackEarly.C0573
import SingleBlackEarly.C0574
import SingleBlackEarly.C0575
import SingleBlackEarly.C0576
import SingleBlackEarly.C0577
import SingleBlackEarly.C0578
import SingleBlackEarly.C0579
import SingleBlackEarly.C0580
import SingleBlackEarly.C0581
import SingleBlackEarly.C0582
import SingleBlackEarly.C0583
import SingleBlackEarly.C0584
import SingleBlackEarly.C0585
import SingleBlackEarly.C0586
import SingleBlackEarly.C0587
import SingleBlackEarly.C0588
import SingleBlackEarly.C0589
import SingleBlackEarly.C0590
import SingleBlackEarly.C0591

namespace LangtonsAnt

def sbGroup15 : List Point :=
  [(18, -8), (17, -8), (18, -6), (19, -6), (19, -7), (19, -5), (20, -5), (20, -6), (18, -5), (18, -4), (19, -4), (19, -3), (20, -3), (20, -4), (18, -3), (18, -2), (19, -2), (17, -2), (17, -3), (19, -1), (20, -1), (20, -2), (18, -1), (20, 0), (21, 0), (21, -1), (19, 0), (20, 1), (19, 5), (20, 5), (20, 4), (20, 6), (21, 6), (21, 5), (19, 6), (19, 13), (20, 13)]

theorem sbGroup15_ok : forall q, q ∈ sbGroup15 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup15, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell0555
  · exact checkSingleBlackFast_sound sbCell0556
  · exact checkSingleBlackFast_sound sbCell0557
  · exact checkSingleBlackFast2_sound sbCell0558
  · exact checkSingleBlackFast_sound sbCell0559
  · exact checkSingleBlackFast2_sound sbCell0560
  · exact checkSingleBlackFast_sound sbCell0561
  · exact checkSingleBlackFast_sound sbCell0562
  · exact checkSingleBlackFast_sound sbCell0563
  · exact checkSingleBlackFast_sound sbCell0564
  · exact checkSingleBlackFast_sound sbCell0565
  · exact checkSingleBlackFast_sound sbCell0566
  · exact checkSingleBlackFast_sound sbCell0567
  · exact checkSingleBlackFast_sound sbCell0568
  · exact checkSingleBlackFast_sound sbCell0569
  · exact checkSingleBlackFast2_sound sbCell0570
  · exact checkSingleBlackFast_sound sbCell0571
  · exact checkSingleBlackFast2_sound sbCell0572
  · exact checkSingleBlackFast_sound sbCell0573
  · exact checkSingleBlackFast_sound sbCell0574
  · exact checkSingleBlackFast_sound sbCell0575
  · exact checkSingleBlackFast_sound sbCell0576
  · exact checkSingleBlackFast_sound sbCell0577
  · exact checkSingleBlack_sound sbCell0578
  · exact checkSingleBlackFast_sound sbCell0579
  · exact checkSingleBlackFast2_sound sbCell0580
  · exact checkSingleBlackFast_sound sbCell0581
  · exact checkSingleBlackFast2_sound sbCell0582
  · exact checkSingleBlackFast_sound sbCell0583
  · exact checkSingleBlackFast_sound sbCell0584
  · exact checkSingleBlackFast_sound sbCell0585
  · exact checkSingleBlackFast_sound sbCell0586
  · exact checkSingleBlackFast_sound sbCell0587
  · exact checkSingleBlackFast2_sound sbCell0588
  · exact checkSingleBlackFast_sound sbCell0589
  · exact checkSingleBlackFast_sound sbCell0590
  · exact checkSingleBlackFast_sound sbCell0591

end LangtonsAnt
