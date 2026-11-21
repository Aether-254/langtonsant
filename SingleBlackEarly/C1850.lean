import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1850 : checkSingleBlackFast2 (-61, -38) 19645 .east (28, 13) (5, -47) = true := by
  decide +kernel

end LangtonsAnt
