import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2160 : checkSingleBlackFast2 (-87, -66) 16210 .north (37, 25) (-64, -36) = true := by
  decide +kernel

end LangtonsAnt
