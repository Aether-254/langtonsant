import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1462 : checkSingleBlack (-22, -2) 45874 .north (0, -3) (-39, -18) = true := by
  decide +kernel

end LangtonsAnt
