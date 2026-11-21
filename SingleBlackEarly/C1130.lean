import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1130 : checkSingleBlackFast2 (26, -16) 10976 .north (-5, 1) (-29, 3) = true := by
  decide +kernel

end LangtonsAnt
