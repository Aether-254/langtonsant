import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0640 : checkSingleBlackFast (10, -9) 9452 .north (2, -4) (-22, -2) = true := by
  decide +kernel

end LangtonsAnt
