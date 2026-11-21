import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0298 : checkSingleBlackFast (8, 12) 6350 .south (-18, -9) (-23, -10) = true := by
  decide +kernel

end LangtonsAnt
