import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0435 : checkSingleBlackFast2 (18, 5) 18965 .west (-10, 3) (-29, -25) = true := by
  decide +kernel

end LangtonsAnt
