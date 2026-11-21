import SingleBlackEarly.S1923_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1923 : (singleBlackFrame (-65, -46) .east (36, 17)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1923 : checkWideEntry (weight ((-67, 1) : Point))
    (highwaySeed.translate (-67, 1)) 3129 sbSegState1923_6 = true := by
  decide +kernel

theorem sbCell1923 : EventuallyStandard (singleBlack (-65, -46)) := by
  have h1 := checkSegment_sound' sbSeg1923_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1923_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1923_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1923_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1923_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1923_6)
  exact singleBlack_of_segments (o := (-67, 1)) sbBox1923 h6 sbEntry1923

end LangtonsAnt
