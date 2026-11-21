import SingleBlackEarly.S1769_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1769 : (singleBlackFrame (-51, -32) .east (29, 10)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1769 : checkWideEntry (weight ((-60, -6) : Point))
    (highwaySeed.translate (-60, -6)) 1673 sbSegState1769_6 = true := by
  decide +kernel

theorem sbCell1769 : EventuallyStandard (singleBlack (-51, -32)) := by
  have h1 := checkSegment_sound' sbSeg1769_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1769_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1769_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1769_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1769_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1769_6)
  exact singleBlack_of_segments (o := (-60, -6)) sbBox1769 h6 sbEntry1769

end LangtonsAnt
