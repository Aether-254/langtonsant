import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2209 : checkSingleBlack (-91, -72) 77833 .east (49, 30) (-80, 14) = true := by
  decide +kernel

end LangtonsAnt
