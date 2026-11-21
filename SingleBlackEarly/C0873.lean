import SingleBlackEarly.S0873_5

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox0873 : (singleBlackFrame (-9, 1) .north (3, -2)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry0873 : checkWideEntry (weight ((-45, -16) : Point))
    (highwaySeed.translate (-45, -16)) 7896 sbSegState0873_5 = true := by
  decide +kernel

theorem sbCell0873 : EventuallyStandard (singleBlack (-9, 1)) := by
  have h1 := checkSegment_sound' sbSeg0873_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg0873_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg0873_3)
  have h4 := segment_chain h3 (checkSegment_sound' sbSeg0873_4)
  have h5 := segment_chain h4 (checkSegment_sound' sbSeg0873_5)
  exact singleBlack_of_segments (o := (-45, -16)) sbBox0873 h5 sbEntry0873

end LangtonsAnt
