import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1385 : checkSingleBlackFast2 (-18, 5) 15308 .north (-8, 3) (-2, -25) = true := by
  decide +kernel

end LangtonsAnt
