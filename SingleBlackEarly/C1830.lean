import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1830 : checkSingleBlack (-57, -36) 14650 .north (22, 10) (-49, -21) = true := by
  decide +kernel

end LangtonsAnt
