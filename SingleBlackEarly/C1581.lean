import SingleBlackEarly.S1581_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1581 : (singleBlackFrame (-36, -11) .west (3, 17)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1581 : checkWideEntry (weight ((-49, -4) : Point))
    (highwaySeed.translate (-49, -4)) 8237 sbSegState1581_5 = true := by
  decide +kernel

theorem sbCell1581 : EventuallyStandard (singleBlack (-36, -11)) := by
  have h1 := checkSegment_sound' sbSeg1581_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1581_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1581_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1581_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1581_5)
  exact singleBlack_of_segments (o := (-49, -4)) sbBox1581 h5 sbEntry1581

end LangtonsAnt
