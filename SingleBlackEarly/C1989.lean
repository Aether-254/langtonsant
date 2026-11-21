import SingleBlackEarly.S1989_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1989 : (singleBlackFrame (-71, -52) .east (39, 20)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1989 : checkWideEntry (weight ((-70, 4) : Point))
    (highwaySeed.translate (-70, 4)) 3753 sbSegState1989_6 = true := by
  decide +kernel

theorem sbCell1989 : EventuallyStandard (singleBlack (-71, -52)) := by
  have h1 := checkSegment_sound' sbSeg1989_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1989_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1989_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1989_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1989_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1989_6)
  exact singleBlack_of_segments (o := (-70, 4)) sbBox1989 h6 sbEntry1989

end LangtonsAnt
