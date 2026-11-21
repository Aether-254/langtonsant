import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0145 : checkSingleBlackFast (8, 3) 3498 .south (-10, -2) (-15, 1) = true := by
  decide +kernel

end LangtonsAnt
