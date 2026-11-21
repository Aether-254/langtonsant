import SingleBlackEarly.S1901_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1901 : (singleBlackFrame (-63, -44) .east (35, 16)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1901 : checkWideEntry (weight ((-66, 0) : Point))
    (highwaySeed.translate (-66, 0)) 2921 sbSegState1901_6 = true := by
  decide +kernel

theorem sbCell1901 : EventuallyStandard (singleBlack (-63, -44)) := by
  have h1 := checkSegment_sound' sbSeg1901_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1901_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1901_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1901_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1901_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1901_6)
  exact singleBlack_of_segments (o := (-66, 0)) sbBox1901 h6 sbEntry1901

end LangtonsAnt
