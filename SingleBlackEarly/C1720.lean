import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1720 : checkSingleBlack (-47, -26) 14130 .north (17, 5) (-44, -16) = true := by
  decide +kernel

end LangtonsAnt
