import SingleBlackEarly.S0923_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox0923 : (singleBlackFrame (-11, 13) .south (-17, 9)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry0923 : checkWideEntry (weight ((-46, -22) : Point))
    (highwaySeed.translate (-46, -22)) 9746 sbSegState0923_5 = true := by
  decide +kernel

theorem sbCell0923 : EventuallyStandard (singleBlack (-11, 13)) := by
  have h1 := checkSegment_sound' sbSeg0923_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg0923_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg0923_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg0923_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg0923_5)
  exact singleBlack_of_segments (o := (-46, -22)) sbBox0923 h5 sbEntry0923

end LangtonsAnt
