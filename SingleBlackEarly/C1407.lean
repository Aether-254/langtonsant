import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1407 : checkSingleBlackFast2 (-20, 3) 15340 .north (-2, -1) (4, -29) = true := by
  decide +kernel

end LangtonsAnt
