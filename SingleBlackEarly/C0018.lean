import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0018 : checkSingleBlack (-1, -4) 12960 .north (5, 2) (-23, -16) = true := by
  decide +kernel

end LangtonsAnt
