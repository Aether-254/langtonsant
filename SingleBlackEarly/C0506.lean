import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0506 : checkSingleBlack (-6, 0) 13212 .north (-2, 5) (2, -25) = true := by
  decide +kernel

end LangtonsAnt
