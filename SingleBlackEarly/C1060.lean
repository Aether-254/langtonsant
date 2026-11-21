import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1060 : checkSingleBlackFast2 (-13, 0) 11572 .north (3, -3) (-27, -5) = true := by
  decide +kernel

end LangtonsAnt
