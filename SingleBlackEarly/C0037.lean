import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0037 : checkSingleBlackFast (-2, 3) 1280 .north (4, 2) (-8, -6) = true := by
  decide +kernel

end LangtonsAnt
