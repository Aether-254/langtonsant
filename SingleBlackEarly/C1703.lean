import SingleBlackEarly.S1703_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1703 : (singleBlackFrame (-45, -26) .west (25, 19)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1703 : checkWideEntry (weight ((-44, -21) : Point))
    (highwaySeed.translate (-44, -21)) 11891 sbSegState1703_5 = true := by
  decide +kernel

theorem sbCell1703 : EventuallyStandard (singleBlack (-45, -26)) := by
  have h1 := checkSegment_sound' sbSeg1703_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1703_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1703_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1703_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1703_5)
  exact singleBlack_of_segments (o := (-44, -21)) sbBox1703 h5 sbEntry1703

end LangtonsAnt
