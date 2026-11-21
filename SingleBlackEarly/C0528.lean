import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0528 : checkSingleBlackFast2 (1, -6) 11996 .south (-6, -14) (-22, -4) = true := by
  decide +kernel

end LangtonsAnt
