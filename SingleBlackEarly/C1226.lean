import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1226 : checkSingleBlackFast2 (9, 19) 12716 .north (-5, -1) (-29, 1) = true := by
  decide +kernel

end LangtonsAnt
