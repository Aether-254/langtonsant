import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1852 : checkSingleBlack (-59, -38) 14754 .north (23, 11) (-50, -22) = true := by
  decide +kernel

end LangtonsAnt
