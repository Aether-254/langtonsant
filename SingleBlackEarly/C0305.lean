import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0305 : checkSingleBlackFast2 (5, 12) 16243 .east (0, -10) (-29, -12) = true := by
  decide +kernel

end LangtonsAnt
