import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2204 : checkSingleBlackFast2 (-91, -70) 16418 .north (39, 27) (-66, -38) = true := by
  decide +kernel

end LangtonsAnt
