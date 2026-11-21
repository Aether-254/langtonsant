import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0297 : checkSingleBlackFast2 (8, 11) 15100 .north (-11, -9) (-25, -19) = true := by
  decide +kernel

end LangtonsAnt
