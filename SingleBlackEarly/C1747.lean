import SingleBlackEarly.S1747_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1747 : (singleBlackFrame (-49, -30) .east (28, 9)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1747 : checkWideEntry (weight ((-59, -7) : Point))
    (highwaySeed.translate (-59, -7)) 1465 sbSegState1747_6 = true := by
  decide +kernel

theorem sbCell1747 : EventuallyStandard (singleBlack (-49, -30)) := by
  have h1 := checkSegment_sound' sbSeg1747_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1747_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1747_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1747_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1747_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1747_6)
  exact singleBlack_of_segments (o := (-59, -7)) sbBox1747 h6 sbEntry1747

end LangtonsAnt
