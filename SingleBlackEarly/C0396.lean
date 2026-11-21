import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0396 : checkSingleBlackFast2 (12, -5) 12743 .west (-11, 0) (-23, -21) = true := by
  decide +kernel

end LangtonsAnt
