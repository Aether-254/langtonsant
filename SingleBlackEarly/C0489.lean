import SingleBlackEarly.S0489_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox0489 : (singleBlackFrame (6, 15) .north (2, -10)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry0489 : checkWideEntry (weight ((-54, -22) : Point))
    (highwaySeed.translate (-54, -22)) 7688 sbSegState0489_5 = true := by
  decide +kernel

theorem sbCell0489 : EventuallyStandard (singleBlack (6, 15)) := by
  have h1 := checkSegment_sound' sbSeg0489_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg0489_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg0489_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg0489_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg0489_5)
  exact singleBlack_of_segments (o := (-54, -22)) sbBox0489 h5 sbEntry0489

end LangtonsAnt
