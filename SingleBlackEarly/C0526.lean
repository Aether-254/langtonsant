import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0526 : checkSingleBlack (0, -6) 41380 .south (1, -9) (-37, -17) = true := by
  decide +kernel

end LangtonsAnt
