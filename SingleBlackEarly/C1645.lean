import SingleBlackEarly.S1645_4

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1645 : (singleBlackFrame (-43, -15) .north (21, 13)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1645 : checkWideEntry (weight ((-43, -9) : Point))
    (highwaySeed.translate (-43, -9)) 6968 sbSegState1645_4 = true := by
  decide +kernel

theorem sbCell1645 : EventuallyStandard (singleBlack (-43, -15)) := by
  have h1 := checkSegment_sound' sbSeg1645_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1645_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1645_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1645_4)
  exact singleBlack_of_segments (o := (-43, -9)) sbBox1645 h4 sbEntry1645

end LangtonsAnt
