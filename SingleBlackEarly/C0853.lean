import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0853 : checkSingleBlackFast (-8, 8) 12498 .north (0, -1) (-27, -14) = true := by
  decide +kernel

end LangtonsAnt
