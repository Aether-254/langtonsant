import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0864 : checkSingleBlackFast2 (-8, 2) 11375 .east (-3, -10) (-25, -3) = true := by
  decide +kernel

end LangtonsAnt
