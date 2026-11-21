import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1757 : checkSingleBlackFast2 (-52, -27) 17499 .east (14, 17) (-8, -34) = true := by
  decide +kernel

end LangtonsAnt
