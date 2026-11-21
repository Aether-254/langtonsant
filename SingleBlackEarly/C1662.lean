import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1662 : checkSingleBlackFast2 (-43, -17) 11580 .north (10, 2) (-36, -18) = true := by
  decide +kernel

end LangtonsAnt
