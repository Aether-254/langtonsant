import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2051 : checkSingleBlack (-77, -57) 46306 .north (50, 33) (-77, -16) = true := by
  decide +kernel

end LangtonsAnt
