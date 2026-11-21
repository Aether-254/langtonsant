import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0358 : checkSingleBlackFast (11, -2) 5850 .south (-8, -9) (-15, -14) = true := by
  decide +kernel

end LangtonsAnt
