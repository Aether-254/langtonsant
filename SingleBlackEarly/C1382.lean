import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1382 : checkSingleBlackFast2 (-17, 8) 15304 .north (-8, 3) (-2, -25) = true := by
  decide +kernel

end LangtonsAnt
