import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2146 : checkSingleBlack (-87, -61) 13868 .north (32, 24) (-58, -40) = true := by
  decide +kernel

end LangtonsAnt
