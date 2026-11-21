import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0940 : checkSingleBlackFast2 (21, 7) 12092 .south (-13, -2) (-27, -18) = true := by
  decide +kernel

end LangtonsAnt
