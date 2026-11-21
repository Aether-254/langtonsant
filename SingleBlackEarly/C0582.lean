import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0582 : checkSingleBlackFast2 (20, 1) 18439 .east (-10, -1) (-20, -26) = true := by
  decide +kernel

end LangtonsAnt
