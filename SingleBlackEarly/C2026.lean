import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2026 : checkSingleBlackFast (-77, -54) 20477 .east (36, 21) (13, -55) = true := by
  decide +kernel

end LangtonsAnt
