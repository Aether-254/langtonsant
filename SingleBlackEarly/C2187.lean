import SingleBlackEarly.S2187_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox2187 : (singleBlackFrame (-89, -70) .east (48, 29)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry2187 : checkWideEntry (weight ((-79, 13) : Point))
    (highwaySeed.translate (-79, 13)) 5625 sbSegState2187_6 = true := by
  decide +kernel

theorem sbCell2187 : EventuallyStandard (singleBlack (-89, -70)) := by
  have h1 := checkSegment_sound' sbSeg2187_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg2187_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg2187_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg2187_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg2187_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg2187_6)
  exact singleBlack_of_segments (o := (-79, 13)) sbBox2187 h6 sbEntry2187

end LangtonsAnt
