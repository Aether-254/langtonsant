import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1022 : checkSingleBlack (-6, 20) 13297 .east (-2, -9) (-29, -21) = true := by
  decide +kernel

end LangtonsAnt
