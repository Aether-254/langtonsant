import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0830 : checkSingleBlackFast2 (23, 2) 15907 .east (-10, 0) (-21, -26) = true := by
  decide +kernel

end LangtonsAnt
