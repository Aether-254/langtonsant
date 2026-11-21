import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1508 : checkSingleBlackFast2 (-29, -3) 10852 .north (3, 0) (-29, -6) = true := by
  decide +kernel

end LangtonsAnt
