import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0485 : checkSingleBlackFast (8, 15) 14315 .east (4, -5) (-24, -22) = true := by
  decide +kernel

end LangtonsAnt
