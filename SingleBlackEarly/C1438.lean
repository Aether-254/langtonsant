import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1438 : checkSingleBlackFast2 (-20, -2) 18272 .north (0, -6) (-34, -14) = true := by
  decide +kernel

end LangtonsAnt
