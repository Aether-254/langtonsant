import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1078 : checkSingleBlackFast2 (-14, -7) 10560 .north (0, 0) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
