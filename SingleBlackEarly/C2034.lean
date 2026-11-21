import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2034 : checkSingleBlackFast2 (-74, -54) 16756 .north (32, 22) (-58, -38) = true := by
  decide +kernel

end LangtonsAnt
