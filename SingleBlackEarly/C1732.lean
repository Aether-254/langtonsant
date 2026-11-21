import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1732 : checkSingleBlack (-51, -24) 18314 .north (17, 10) (-44, -23) = true := by
  decide +kernel

end LangtonsAnt
