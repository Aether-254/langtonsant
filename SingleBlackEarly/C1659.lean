import SingleBlackEarly.S1659_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1659 : (singleBlackFrame (-41, -22) .east (24, 5)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1659 : checkWideEntry (weight ((-55, -11) : Point))
    (highwaySeed.translate (-55, -11)) 1385 sbSegState1659_6 = true := by
  decide +kernel

theorem sbCell1659 : EventuallyStandard (singleBlack (-41, -22)) := by
  have h1 := checkSegment_sound' sbSeg1659_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1659_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1659_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1659_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1659_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1659_6)
  exact singleBlack_of_segments (o := (-55, -11)) sbBox1659 h6 sbEntry1659

end LangtonsAnt
