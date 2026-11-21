import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1820 : checkSingleBlackFast2 (-59, -32) 18730 .north (21, 14) (-48, -27) = true := by
  decide +kernel

end LangtonsAnt
