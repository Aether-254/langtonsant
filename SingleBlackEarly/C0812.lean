import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0812 : checkSingleBlackFast2 (25, -3) 15035 .east (-10, 2) (-23, -26) = true := by
  decide +kernel

end LangtonsAnt
