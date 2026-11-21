import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1178 : checkSingleBlackFast2 (26, -2) 10488 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
