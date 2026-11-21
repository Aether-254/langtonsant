import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1058 : checkSingleBlackFast2 (-14, -1) 11942 .north (-2, 0) (-19, -15) = true := by
  decide +kernel

end LangtonsAnt
