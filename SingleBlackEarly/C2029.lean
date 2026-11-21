import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2029 : checkSingleBlack (-75, -55) 46202 .north (49, 32) (-76, -15) = true := by
  decide +kernel

end LangtonsAnt
