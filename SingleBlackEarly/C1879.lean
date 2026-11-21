import SingleBlackEarly.S1879_6

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox1879 : (singleBlackFrame (-61, -42) .east (34, 15)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry1879 : checkWideEntry (weight ((-65, -1) : Point))
    (highwaySeed.translate (-65, -1)) 2713 sbSegState1879_6 = true := by
  decide +kernel

theorem sbCell1879 : EventuallyStandard (singleBlack (-61, -42)) := by
  have h1 := checkSegment_sound' sbSeg1879_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg1879_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg1879_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg1879_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg1879_5)
  have h6 := segment_chain h5 (checkSegment_sound' sbSeg1879_6)
  exact singleBlack_of_segments (o := (-65, -1)) sbBox1879 h6 sbEntry1879

end LangtonsAnt
