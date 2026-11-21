import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1439 : checkSingleBlackFast (-21, -2) 12511 .east (1, -7) (-26, -15) = true := by
  decide +kernel

end LangtonsAnt
