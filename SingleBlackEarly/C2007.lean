import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2007 : checkSingleBlack (-73, -53) 46098 .north (48, 31) (-75, -14) = true := by
  decide +kernel

end LangtonsAnt
