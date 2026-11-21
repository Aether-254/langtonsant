import SingleBlackEarly.S0227_3

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbBox0227 : (singleBlackFrame (7, 8) .west (1, 6)).black.all
    (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbEntry0227 : checkWideEntry (weight ((-39, -9) : Point))
    (highwaySeed.translate (-39, -9)) 8823 sbSegState0227_3 = true := by
  decide +kernel

theorem sbCell0227 : EventuallyStandard (singleBlack (7, 8)) := by
  have h1 := checkSegment_sound' sbSeg0227_1
  have h2 := segment_chain h1 (checkSegment_sound' sbSeg0227_2)
  have h3 := segment_chain h2 (checkSegment_sound' sbSeg0227_3)
  exact singleBlack_of_segments (o := (-39, -9)) sbBox0227 h3 sbEntry0227

end LangtonsAnt
