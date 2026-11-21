import SingleBlackEarly.S1813_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1813 : (singleBlackFrame (-55, -36) .east (31, 12)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1813 : checkWideEntry (weight ((-62, -4) : Point))
    (highwaySeed.translate (-62, -4)) 2089 sbSegState1813_6 = true := by
  decide +kernel

theorem sbCell1813 : EventuallyStandard (singleBlack (-55, -36)) := by
  have h1 := checkSegment_sound' sbSeg1813_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1813_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1813_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1813_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1813_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1813_6)
  exact singleBlack_of_segments (o := (-62, -4)) sbBox1813 h6 sbEntry1813

end LangtonsAnt
