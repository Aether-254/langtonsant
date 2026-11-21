import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1892 : checkSingleBlack (-64, -40) 14619 .west (19, 29) (-48, 9) = true := by
  decide +kernel

end LangtonsAnt
