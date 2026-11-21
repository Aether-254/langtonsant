import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0674 : checkSingleBlack (16, -12) 45973 .east (5, -16) (-42, -20) = true := by
  decide +kernel

end LangtonsAnt
