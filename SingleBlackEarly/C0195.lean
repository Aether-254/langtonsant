import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0195 : checkSingleBlackFast (10, 2) 1947 .east (1, -5) (-8, -7) = true := by
  decide +kernel

end LangtonsAnt
