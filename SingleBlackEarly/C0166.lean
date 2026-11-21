import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0166 : checkSingleBlackFast2 (-5, 6) 10878 .north (15, -5) (-28, -14) = true := by
  decide +kernel

end LangtonsAnt
