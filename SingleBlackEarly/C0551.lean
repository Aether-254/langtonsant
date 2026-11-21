import SingleBlackEarly.S0551_3

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox0551 : (singleBlackFrame (17, -6) .north (17, 0)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry0551 : checkWideEntry (weight ((-37, -20) : Point))
    (highwaySeed.translate (-37, -20)) 4228 sbSegState0551_3 = true := by
  decide +kernel

theorem sbCell0551 : EventuallyStandard (singleBlack (17, -6)) := by
  have h1 := checkSegment_sound' sbSeg0551_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg0551_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg0551_3)
  exact singleBlack_of_segments (o := (-37, -20)) sbBox0551 h3 sbEntry0551

end LangtonsAnt
