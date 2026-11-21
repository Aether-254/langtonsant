import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0999 : checkSingleBlackFast (-8, 15) 8376 .north (0, -3) (-24, -1) = true := by
  decide +kernel

end LangtonsAnt
