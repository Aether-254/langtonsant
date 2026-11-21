import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1591 : checkSingleBlackFast (-34, -15) 19568 .north (19, 15) (-45, -7) = true := by
  decide +kernel

end LangtonsAnt
