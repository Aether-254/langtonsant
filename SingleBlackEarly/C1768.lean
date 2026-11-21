import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1768 : checkSingleBlackFast2 (-50, -32) 28043 .east (28, 16) (-13, -38) = true := by
  decide +kernel

end LangtonsAnt
