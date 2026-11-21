import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1611 : checkSingleBlackFast (-37, -17) 35708 .north (11, 14) (-13, -44) = true := by
  decide +kernel

end LangtonsAnt
