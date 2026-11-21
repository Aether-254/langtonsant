import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0206 : checkSingleBlackFast (10, 5) 1991 .east (0, -5) (-8, -8) = true := by
  decide +kernel

end LangtonsAnt
