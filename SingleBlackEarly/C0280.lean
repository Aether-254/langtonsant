import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0280 : checkSingleBlackFast2 (14, 10) 15592 .north (-8, 8) (-16, -20) = true := by
  decide +kernel

end LangtonsAnt
