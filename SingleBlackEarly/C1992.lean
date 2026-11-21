import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1992 : checkSingleBlack (-73, -47) 13140 .north (25, 17) (-51, -33) = true := by
  decide +kernel

end LangtonsAnt
