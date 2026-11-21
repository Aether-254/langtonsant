import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1674 : checkSingleBlackFast2 (-45, -22) 18813 .east (20, 5) (-3, -39) = true := by
  decide +kernel

end LangtonsAnt
