import SingleBlackEarly.S1655_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1655 : (singleBlackFrame (-41, -21) .south (16, 8)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1655 : checkWideEntry (weight ((-54, -20) : Point))
    (highwaySeed.translate (-54, -20)) 952 sbSegState1655_5 = true := by
  decide +kernel

theorem sbCell1655 : EventuallyStandard (singleBlack (-41, -21)) := by
  have h1 := checkSegment_sound' sbSeg1655_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1655_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1655_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1655_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1655_5)
  exact singleBlack_of_segments (o := (-54, -20)) sbBox1655 h5 sbEntry1655

end LangtonsAnt
