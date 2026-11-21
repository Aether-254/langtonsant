import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0882 : checkSingleBlack (-10, -2) 14553 .east (-6, -7) (-27, -7) = true := by
  decide +kernel

end LangtonsAnt
