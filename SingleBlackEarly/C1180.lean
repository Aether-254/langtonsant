import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1180 : checkSingleBlackFast2 (27, 0) 11688 .north (-5, 0) (-29, 2) = true := by
  decide +kernel

end LangtonsAnt
