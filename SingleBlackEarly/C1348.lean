import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1348 : checkSingleBlackFast2 (-17, 11) 10882 .north (2, 0) (-29, 1) = true := by
  decide +kernel

end LangtonsAnt
