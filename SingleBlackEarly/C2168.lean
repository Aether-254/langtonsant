import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2168 : checkSingleBlack (-89, -63) 13972 .north (33, 25) (-59, -41) = true := by
  decide +kernel

end LangtonsAnt
