import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1473 : checkSingleBlackFast (-26, -3) 19612 .north (2, -7) (-36, -5) = true := by
  decide +kernel

end LangtonsAnt
