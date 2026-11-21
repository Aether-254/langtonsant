import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0498 : checkSingleBlackFast2 (1, 16) 16489 .east (-20, -6) (-22, -27) = true := by
  decide +kernel

end LangtonsAnt
