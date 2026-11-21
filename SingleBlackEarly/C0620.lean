import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0620 : checkSingleBlackFast2 (5, -7) 16449 .east (1, -1) (-11, -26) = true := by
  decide +kernel

end LangtonsAnt
