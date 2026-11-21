import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1889 : checkSingleBlack (-64, -39) 18123 .east (20, 23) (-2, -40) = true := by
  decide +kernel

end LangtonsAnt
