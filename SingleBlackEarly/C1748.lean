import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1748 : checkSingleBlackFast2 (-48, -28) 15404 .north (19, 9) (-45, -25) = true := by
  decide +kernel

end LangtonsAnt
