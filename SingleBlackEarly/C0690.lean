import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0690 : checkSingleBlackFast2 (20, -12) 18364 .south (-13, 4) (-19, -26) = true := by
  decide +kernel

end LangtonsAnt
