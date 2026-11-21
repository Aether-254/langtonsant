import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1292 : checkSingleBlackFast2 (-4, 20) 10803 .east (-4, -8) (-27, -18) = true := by
  decide +kernel

end LangtonsAnt
