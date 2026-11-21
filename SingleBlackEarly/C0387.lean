import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0387 : checkSingleBlackFast (16, 2) 9450 .north (1, 7) (-8, -18) = true := by
  decide +kernel

end LangtonsAnt
