import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1765 : checkSingleBlack (-51, -31) 44954 .north (37, 20) (-64, -3) = true := by
  decide +kernel

end LangtonsAnt
