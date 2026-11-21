import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0052 : checkSingleBlackFast2 (3, -2) 16889 .east (-9, -14) (-30, 2) = true := by
  decide +kernel

end LangtonsAnt
