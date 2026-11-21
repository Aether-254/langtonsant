import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0846 : checkSingleBlackFast2 (-5, 9) 15696 .north (-7, 7) (-5, -25) = true := by
  decide +kernel

end LangtonsAnt
