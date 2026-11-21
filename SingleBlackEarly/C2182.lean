import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2182 : checkSingleBlackFast2 (-89, -68) 16314 .north (38, 26) (-65, -37) = true := by
  decide +kernel

end LangtonsAnt
