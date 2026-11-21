import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1336 : checkSingleBlackFast2 (-14, 14) 17188 .north (-7, 3) (-5, -29) = true := by
  decide +kernel

end LangtonsAnt
