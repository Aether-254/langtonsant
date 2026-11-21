import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1808 : checkSingleBlack (-55, -34) 14546 .north (21, 9) (-48, -20) = true := by
  decide +kernel

end LangtonsAnt
