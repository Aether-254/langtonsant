import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0780 : checkSingleBlackFast2 (25, -14) 10660 .north (-2, -1) (-26, 1) = true := by
  decide +kernel

end LangtonsAnt
