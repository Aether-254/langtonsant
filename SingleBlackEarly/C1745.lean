import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1745 : checkSingleBlackFast2 (-48, -29) 20296 .north (26, 22) (-52, -14) = true := by
  decide +kernel

end LangtonsAnt
