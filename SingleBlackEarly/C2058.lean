import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2058 : checkSingleBlack (-79, -53) 13452 .north (28, 20) (-54, -36) = true := by
  decide +kernel

end LangtonsAnt
