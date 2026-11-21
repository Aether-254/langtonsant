import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1990 : checkSingleBlackFast2 (-70, -50) 16548 .north (30, 20) (-56, -36) = true := by
  decide +kernel

end LangtonsAnt
