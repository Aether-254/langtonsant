import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2062 : checkSingleBlackFast (-81, -54) 19874 .north (32, 25) (-59, -38) = true := by
  decide +kernel

end LangtonsAnt
