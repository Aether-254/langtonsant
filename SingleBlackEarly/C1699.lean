import SingleBlackEarly.S1699_4

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1699 : (singleBlackFrame (-45, -25) .north (31, 11)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1699 : checkWideEntry (weight ((-64, -6) : Point))
    (highwaySeed.translate (-64, -6)) 6078 sbSegState1699_4 = true := by
  decide +kernel

theorem sbCell1699 : EventuallyStandard (singleBlack (-45, -25)) := by
  have h1 := checkSegment_sound' sbSeg1699_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1699_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1699_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1699_4)
  exact singleBlack_of_segments (o := (-64, -6)) sbBox1699 h4 sbEntry1699

end LangtonsAnt
