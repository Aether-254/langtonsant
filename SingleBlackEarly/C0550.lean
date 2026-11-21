import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0550 : checkSingleBlackFast (10, -3) 6551 .east (0, -7) (-14, -16) = true := by
  decide +kernel

end LangtonsAnt
