import SingleBlackEarly.S1945_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1945 : (singleBlackFrame (-67, -48) .east (37, 18)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1945 : checkWideEntry (weight ((-68, 2) : Point))
    (highwaySeed.translate (-68, 2)) 3337 sbSegState1945_6 = true := by
  decide +kernel

theorem sbCell1945 : EventuallyStandard (singleBlack (-67, -48)) := by
  have h1 := checkSegment_sound' sbSeg1945_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1945_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1945_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1945_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1945_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1945_6)
  exact singleBlack_of_segments (o := (-68, 2)) sbBox1945 h6 sbEntry1945

end LangtonsAnt
