import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1343 : checkSingleBlackFast2 (-15, 11) 15128 .north (-9, 3) (-3, -25) = true := by
  decide +kernel

end LangtonsAnt
