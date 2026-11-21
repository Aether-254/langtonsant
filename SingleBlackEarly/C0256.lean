import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0256 : checkSingleBlackFast2 (13, 10) 16875 .east (-2, -16) (-29, -18) = true := by
  decide +kernel

end LangtonsAnt
