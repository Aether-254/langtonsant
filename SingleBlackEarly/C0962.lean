import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0962 : checkSingleBlack (6, 19) 12976 .north (-5, 5) (-3, -27) = true := by
  decide +kernel

end LangtonsAnt
