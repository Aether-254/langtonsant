import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2050 : checkSingleBlackFast2 (-77, -56) 15690 .north (32, 20) (-59, -31) = true := by
  decide +kernel

end LangtonsAnt
