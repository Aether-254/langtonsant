import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0862 : checkSingleBlackFast2 (-8, 3) 18146 .south (-13, -2) (-36, -17) = true := by
  decide +kernel

end LangtonsAnt
