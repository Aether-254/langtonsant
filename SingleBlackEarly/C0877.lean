import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0877 : checkSingleBlackFast2 (-11, 0) 24745 .east (2, 0) (-36, -11) = true := by
  decide +kernel

end LangtonsAnt
