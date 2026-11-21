import SingleBlackEarly.S1681_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1681 : (singleBlackFrame (-43, -24) .north (41, 21)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1681 : checkWideEntry (weight ((-68, -16) : Point))
    (highwaySeed.translate (-68, -16)) 3922 sbSegState1681_5 = true := by
  decide +kernel

theorem sbCell1681 : EventuallyStandard (singleBlack (-43, -24)) := by
  have h1 := checkSegment_sound' sbSeg1681_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1681_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1681_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1681_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1681_5)
  exact singleBlack_of_segments (o := (-68, -16)) sbBox1681 h5 sbEntry1681

end LangtonsAnt
