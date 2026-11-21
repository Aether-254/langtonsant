import SingleBlackEarly.S1857_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1857 : (singleBlackFrame (-59, -40) .east (33, 14)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1857 : checkWideEntry (weight ((-64, -2) : Point))
    (highwaySeed.translate (-64, -2)) 2505 sbSegState1857_6 = true := by
  decide +kernel

theorem sbCell1857 : EventuallyStandard (singleBlack (-59, -40)) := by
  have h1 := checkSegment_sound' sbSeg1857_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1857_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1857_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1857_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1857_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1857_6)
  exact singleBlack_of_segments (o := (-64, -2)) sbBox1857 h6 sbEntry1857

end LangtonsAnt
