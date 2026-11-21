import SingleBlackEarly.S1615_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1615 : (singleBlackFrame (-37, -18) .west (25, 11)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1615 : checkWideEntry (weight ((-30, -35) : Point))
    (highwaySeed.translate (-30, -35)) 11255 sbSegState1615_5 = true := by
  decide +kernel

theorem sbCell1615 : EventuallyStandard (singleBlack (-37, -18)) := by
  have h1 := checkSegment_sound' sbSeg1615_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1615_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1615_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1615_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1615_5)
  exact singleBlack_of_segments (o := (-30, -35)) sbBox1615 h5 sbEntry1615

end LangtonsAnt
