import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1926 : checkSingleBlackFast2 (-67, -41) 12828 .north (22, 14) (-48, -30) = true := by
  decide +kernel

end LangtonsAnt
