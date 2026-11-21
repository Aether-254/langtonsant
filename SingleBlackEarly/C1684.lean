import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1684 : checkSingleBlackFast2 (-45, -19) 11684 .north (11, 3) (-37, -19) = true := by
  decide +kernel

end LangtonsAnt
