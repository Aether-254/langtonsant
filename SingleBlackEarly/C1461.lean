import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1461 : checkSingleBlackFast (-23, -4) 23278 .north (5, -9) (-38, -2) = true := by
  decide +kernel

end LangtonsAnt
