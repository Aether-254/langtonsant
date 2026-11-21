import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1886 : checkSingleBlackFast2 (-65, -38) 19042 .north (24, 17) (-51, -30) = true := by
  decide +kernel

end LangtonsAnt
