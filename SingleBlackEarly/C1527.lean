import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1527 : checkSingleBlackFast2 (-29, -10) 15381 .east (7, 0) (-16, -30) = true := by
  decide +kernel

end LangtonsAnt
