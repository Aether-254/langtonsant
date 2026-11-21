import SingleBlackEarly.S1791_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1791 : (singleBlackFrame (-53, -34) .east (30, 11)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1791 : checkWideEntry (weight ((-61, -5) : Point))
    (highwaySeed.translate (-61, -5)) 1881 sbSegState1791_6 = true := by
  decide +kernel

theorem sbCell1791 : EventuallyStandard (singleBlack (-53, -34)) := by
  have h1 := checkSegment_sound' sbSeg1791_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1791_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1791_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1791_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1791_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1791_6)
  exact singleBlack_of_segments (o := (-61, -5)) sbBox1791 h6 sbEntry1791

end LangtonsAnt
