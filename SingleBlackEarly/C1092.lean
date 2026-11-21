import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1092 : checkSingleBlackFast2 (-8, -9) 10684 .north (0, 0) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
