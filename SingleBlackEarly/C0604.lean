import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0604 : checkSingleBlackFast2 (15, 14) 10573 .east (-6, -7) (-27, 1) = true := by
  decide +kernel

end LangtonsAnt
