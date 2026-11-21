import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1713 : checkSingleBlackFast2 (-48, -23) 17291 .east (12, 15) (-10, -32) = true := by
  decide +kernel

end LangtonsAnt
