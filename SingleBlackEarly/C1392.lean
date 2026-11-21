import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1392 : checkSingleBlackFast2 (-18, 3) 16564 .south (0, -5) (-22, -21) = true := by
  decide +kernel

end LangtonsAnt
