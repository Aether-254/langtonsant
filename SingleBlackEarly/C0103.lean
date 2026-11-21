import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0103 : checkSingleBlackFast2 (-3, 6) 16411 .east (5, -12) (-29, -25) = true := by
  decide +kernel

end LangtonsAnt
