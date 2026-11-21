import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0817 : checkSingleBlackFast2 (25, -2) 16688 .north (-10, 6) (-18, -14) = true := by
  decide +kernel

end LangtonsAnt
