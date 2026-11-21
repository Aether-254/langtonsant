import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1682 : checkSingleBlackFast2 (-42, -22) 15092 .north (16, 6) (-42, -22) = true := by
  decide +kernel

end LangtonsAnt
