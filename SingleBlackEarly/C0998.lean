import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0998 : checkSingleBlack (-9, 15) 13375 .east (-2, -5) (-22, -24) = true := by
  decide +kernel

end LangtonsAnt
