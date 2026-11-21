import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1486 : checkSingleBlackFast2 (-27, -1) 10748 .north (2, 0) (-28, -4) = true := by
  decide +kernel

end LangtonsAnt
