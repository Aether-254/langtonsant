import SingleBlackEarly.S1725_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1725 : (singleBlackFrame (-47, -28) .east (27, 8)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1725 : checkWideEntry (weight ((-58, -8) : Point))
    (highwaySeed.translate (-58, -8)) 1257 sbSegState1725_6 = true := by
  decide +kernel

theorem sbCell1725 : EventuallyStandard (singleBlack (-47, -28)) := by
  have h1 := checkSegment_sound' sbSeg1725_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1725_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1725_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1725_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1725_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1725_6)
  exact singleBlack_of_segments (o := (-58, -8)) sbBox1725 h6 sbEntry1725

end LangtonsAnt
