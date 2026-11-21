import SingleBlackEarly.S1012_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1012 : (singleBlackFrame (-13, 6) .north (-16, -2)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1012 : checkWideEntry (weight ((-45, -23) : Point))
    (highwaySeed.translate (-45, -23)) 3602 sbSegState1012_6 = true := by
  decide +kernel

theorem sbCell1012 : EventuallyStandard (singleBlack (-13, 6)) := by
  have h1 := checkSegment_sound' sbSeg1012_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1012_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1012_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1012_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1012_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1012_6)
  exact singleBlack_of_segments (o := (-45, -23)) sbBox1012 h6 sbEntry1012

end LangtonsAnt
