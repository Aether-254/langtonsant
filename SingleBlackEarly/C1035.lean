import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1035 : checkSingleBlackFast2 (-11, 3) 15616 .north (-3, 7) (-1, -25) = true := by
  decide +kernel

end LangtonsAnt
