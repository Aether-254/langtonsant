import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1941 : checkSingleBlack (-67, -47) 45786 .north (45, 28) (-72, -11) = true := by
  decide +kernel

end LangtonsAnt
