import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1787 : checkSingleBlack (-53, -33) 45058 .north (38, 21) (-65, -4) = true := by
  decide +kernel

end LangtonsAnt
