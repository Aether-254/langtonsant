import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0914 : checkSingleBlack (-11, 5) 14624 .north (-2, 7) (-2, -27) = true := by
  decide +kernel

end LangtonsAnt
