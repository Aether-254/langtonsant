import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1320 : checkSingleBlack (-10, 14) 41400 .north (-1, 0) (-5, -38) = true := by
  decide +kernel

end LangtonsAnt
