import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1875 : checkSingleBlack (-61, -41) 45474 .north (42, 25) (-69, -8) = true := by
  decide +kernel

end LangtonsAnt
