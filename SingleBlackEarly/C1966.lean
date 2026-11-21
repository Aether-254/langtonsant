import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1966 : checkSingleBlackFast (-68, -50) 28979 .east (37, 25) (-4, -47) = true := by
  decide +kernel

end LangtonsAnt
