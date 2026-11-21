import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1610 : checkSingleBlack (-37, -16) 13610 .north (12, 0) (-39, -11) = true := by
  decide +kernel

end LangtonsAnt
