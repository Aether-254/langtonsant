import SingleBlackEarly.S1651_4

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1651 : (singleBlackFrame (-42, -20) .west (6, 0)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1651 : checkWideEntry (weight ((-52, -3) : Point))
    (highwaySeed.translate (-52, -3)) 9733 sbSegState1651_4 = true := by
  decide +kernel

theorem sbCell1651 : EventuallyStandard (singleBlack (-42, -20)) := by
  have h1 := checkSegment_sound' sbSeg1651_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1651_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1651_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1651_4)
  exact singleBlack_of_segments (o := (-52, -3)) sbBox1651 h4 sbEntry1651

end LangtonsAnt
