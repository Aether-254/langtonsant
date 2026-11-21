import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1043 : checkSingleBlackFast2 (-12, -3) 15172 .north (3, -3) (-27, -7) = true := by
  decide +kernel

end LangtonsAnt
