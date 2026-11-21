import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0860 : checkSingleBlack (-9, 6) 13244 .north (-5, 6) (-3, -26) = true := by
  decide +kernel

end LangtonsAnt
