import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1823 : checkSingleBlackFast2 (-58, -33) 17811 .east (17, 20) (-5, -37) = true := by
  decide +kernel

end LangtonsAnt
