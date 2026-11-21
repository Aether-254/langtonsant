import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1360 : checkSingleBlackFast2 (-14, 4) 10696 .north (1, 0) (-27, -2) = true := by
  decide +kernel

end LangtonsAnt
