import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1491 : checkSingleBlackFast2 (-29, -1) 16520 .north (10, -7) (-36, -11) = true := by
  decide +kernel

end LangtonsAnt
