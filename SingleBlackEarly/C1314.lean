import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1314 : checkSingleBlackFast2 (-11, 16) 12312 .north (-3, 5) (3, -23) = true := by
  decide +kernel

end LangtonsAnt
