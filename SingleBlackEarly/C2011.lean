import SingleBlackEarly.S2011_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox2011 : (singleBlackFrame (-73, -54) .east (40, 21)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry2011 : checkWideEntry (weight ((-71, 5) : Point))
    (highwaySeed.translate (-71, 5)) 3961 sbSegState2011_6 = true := by
  decide +kernel

theorem sbCell2011 : EventuallyStandard (singleBlack (-73, -54)) := by
  have h1 := checkSegment_sound' sbSeg2011_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg2011_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg2011_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg2011_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg2011_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg2011_6)
  exact singleBlack_of_segments (o := (-71, 5)) sbBox2011 h6 sbEntry2011

end LangtonsAnt
