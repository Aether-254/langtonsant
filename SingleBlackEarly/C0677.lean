import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0677 : checkSingleBlackFast (17, -10) 9900 .north (2, -2) (-22, 0) = true := by
  decide +kernel

end LangtonsAnt
