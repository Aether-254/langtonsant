import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1480 : checkSingleBlackFast2 (-26, -5) 12431 .east (2, -2) (-21, -18) = true := by
  decide +kernel

end LangtonsAnt
