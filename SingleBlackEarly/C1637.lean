import SingleBlackEarly.S1637_4

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1637 : (singleBlackFrame (-39, -20) .east (25, 1)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1637 : checkWideEntry (weight ((-57, -2) : Point))
    (highwaySeed.translate (-57, -2)) 9541 sbSegState1637_4 = true := by
  decide +kernel

theorem sbCell1637 : EventuallyStandard (singleBlack (-39, -20)) := by
  have h1 := checkSegment_sound' sbSeg1637_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1637_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1637_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1637_4)
  exact singleBlack_of_segments (o := (-57, -2)) sbBox1637 h4 sbEntry1637

end LangtonsAnt
