import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2047 : checkSingleBlackFast2 (-78, -56) 19859 .east (29, 23) (-4, -41) = true := by
  decide +kernel

end LangtonsAnt
