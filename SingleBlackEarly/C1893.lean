import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1893 : checkSingleBlackFast2 (-64, -42) 19131 .east (22, 16) (-11, -34) = true := by
  decide +kernel

end LangtonsAnt
