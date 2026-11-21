import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1594 : checkSingleBlack (-34, -14) 14676 .north (12, 2) (-38, -18) = true := by
  decide +kernel

end LangtonsAnt
