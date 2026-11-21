import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1977 : checkSingleBlack (-72, -47) 18539 .east (24, 27) (2, -44) = true := by
  decide +kernel

end LangtonsAnt
