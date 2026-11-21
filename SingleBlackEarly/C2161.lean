import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2161 : checkSingleBlack (-87, -67) 46826 .north (55, 38) (-82, -21) = true := by
  decide +kernel

end LangtonsAnt
