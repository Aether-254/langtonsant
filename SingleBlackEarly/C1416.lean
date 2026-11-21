import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1416 : checkSingleBlackFast2 (-18, 0) 16046 .north (3, -7) (-30, -20) = true := by
  decide +kernel

end LangtonsAnt
