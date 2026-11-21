import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2100 : checkSingleBlackFast2 (-80, -60) 17068 .north (35, 25) (-61, -41) = true := by
  decide +kernel

end LangtonsAnt
