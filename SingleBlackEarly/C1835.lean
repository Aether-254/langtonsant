import SingleBlackEarly.S1835_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1835 : (singleBlackFrame (-57, -38) .east (32, 13)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1835 : checkWideEntry (weight ((-63, -3) : Point))
    (highwaySeed.translate (-63, -3)) 2297 sbSegState1835_6 = true := by
  decide +kernel

theorem sbCell1835 : EventuallyStandard (singleBlack (-57, -38)) := by
  have h1 := checkSegment_sound' sbSeg1835_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1835_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1835_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1835_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1835_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1835_6)
  exact singleBlack_of_segments (o := (-63, -3)) sbBox1835 h6 sbEntry1835

end LangtonsAnt
