import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1321 : checkSingleBlackFast2 (-13, 14) 15784 .north (-8, 3) (-2, -25) = true := by
  decide +kernel

end LangtonsAnt
