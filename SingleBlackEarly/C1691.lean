import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1691 : checkSingleBlackFast2 (-46, -21) 17187 .east (11, 14) (-11, -31) = true := by
  decide +kernel

end LangtonsAnt
