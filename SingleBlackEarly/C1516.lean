import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1516 : checkSingleBlackFast (-29, -7) 22196 .north (2, -6) (-36, -14) = true := by
  decide +kernel

end LangtonsAnt
