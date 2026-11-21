import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0726 : checkSingleBlackFast2 (8, -14) 10448 .north (-3, -2) (-27, 0) = true := by
  decide +kernel

end LangtonsAnt
