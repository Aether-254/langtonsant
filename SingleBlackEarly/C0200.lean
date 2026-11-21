import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0200 : checkSingleBlackFast2 (10, 3) 15040 .north (-5, 5) (-23, -11) = true := by
  decide +kernel

end LangtonsAnt
