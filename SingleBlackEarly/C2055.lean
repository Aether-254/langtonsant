import SingleBlackEarly.S2055_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox2055 : (singleBlackFrame (-77, -58) .east (42, 23)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry2055 : checkWideEntry (weight ((-73, 7) : Point))
    (highwaySeed.translate (-73, 7)) 4377 sbSegState2055_6 = true := by
  decide +kernel

theorem sbCell2055 : EventuallyStandard (singleBlack (-77, -58)) := by
  have h1 := checkSegment_sound' sbSeg2055_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg2055_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg2055_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg2055_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg2055_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg2055_6)
  exact singleBlack_of_segments (o := (-73, 7)) sbBox2055 h6 sbEntry2055

end LangtonsAnt
