import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1347 : checkSingleBlackFast2 (-17, 10) 17632 .north (-8, 4) (-4, -26) = true := by
  decide +kernel

end LangtonsAnt
