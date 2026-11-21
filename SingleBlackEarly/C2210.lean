import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2210 : checkSingleBlackFast2 (-90, -70) 17588 .north (40, 30) (-66, -46) = true := by
  decide +kernel

end LangtonsAnt
