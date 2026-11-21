import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0181 : checkSingleBlackFast (8, -2) 1947 .east (0, -5) (-8, -8) = true := by
  decide +kernel

end LangtonsAnt
