import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1380 : checkSingleBlackFast2 (-19, 8) 15296 .north (-8, 3) (-2, -25) = true := by
  decide +kernel

end LangtonsAnt
