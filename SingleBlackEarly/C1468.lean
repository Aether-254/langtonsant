import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1468 : checkSingleBlackFast2 (-27, 0) 12444 .north (0, 9) (0, -25) = true := by
  decide +kernel

end LangtonsAnt
