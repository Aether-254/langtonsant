import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2099 : checkSingleBlack (-81, -62) 76793 .east (44, 25) (-75, 9) = true := by
  decide +kernel

end LangtonsAnt
