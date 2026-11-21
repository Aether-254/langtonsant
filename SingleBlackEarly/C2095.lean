import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2095 : checkSingleBlack (-81, -61) 46514 .north (52, 35) (-79, -18) = true := by
  decide +kernel

end LangtonsAnt
