import SingleBlackEarly.S1523_4

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1523 : (singleBlackFrame (-29, -9) .west (10, 15)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1523 : checkWideEntry (weight ((-53, 9) : Point))
    (highwaySeed.translate (-53, 9)) 7705 sbSegState1523_4 = true := by
  decide +kernel

theorem sbCell1523 : EventuallyStandard (singleBlack (-29, -9)) := by
  have h1 := checkSegment_sound' sbSeg1523_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1523_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1523_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1523_4)
  exact singleBlack_of_segments (o := (-53, 9)) sbBox1523 h4 sbEntry1523

end LangtonsAnt
