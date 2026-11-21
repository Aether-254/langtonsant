import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1453 : checkSingleBlackFast2 (-24, -2) 18192 .north (1, 4) (-3, -34) = true := by
  decide +kernel

end LangtonsAnt
