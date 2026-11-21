import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1578 : checkSingleBlackFast (-37, -10) 19806 .north (5, -6) (-38, -21) = true := by
  decide +kernel

end LangtonsAnt
