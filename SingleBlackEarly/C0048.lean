import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0048 : checkSingleBlackFast (2, -3) 2515 .east (2, -2) (-11, -6) = true := by
  decide +kernel

end LangtonsAnt
