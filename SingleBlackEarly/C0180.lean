import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0180 : checkSingleBlackFast (8, -1) 4438 .north (-8, 9) (-17, -12) = true := by
  decide +kernel

end LangtonsAnt
