import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1028 : checkSingleBlack (-8, 17) 14203 .east (4, -7) (-22, -24) = true := by
  decide +kernel

end LangtonsAnt
