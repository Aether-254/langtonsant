import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1918 : checkSingleBlackFast2 (-65, -44) 15066 .north (26, 14) (-53, -25) = true := by
  decide +kernel

end LangtonsAnt
