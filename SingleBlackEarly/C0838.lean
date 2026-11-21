import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0838 : checkSingleBlack (0, 13) 14205 .east (-9, -14) (-28, -2) = true := by
  decide +kernel

end LangtonsAnt
