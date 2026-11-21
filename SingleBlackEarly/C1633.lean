import SingleBlackEarly.S1633_4

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1633 : (singleBlackFrame (-39, -19) .north (13, 19)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1633 : checkWideEntry (weight ((-19, -47) : Point))
    (highwaySeed.translate (-19, -47)) 2188 sbSegState1633_4 = true := by
  decide +kernel

theorem sbCell1633 : EventuallyStandard (singleBlack (-39, -19)) := by
  have h1 := checkSegment_sound' sbSeg1633_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1633_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1633_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1633_4)
  exact singleBlack_of_segments (o := (-19, -47)) sbBox1633 h4 sbEntry1633

end LangtonsAnt
