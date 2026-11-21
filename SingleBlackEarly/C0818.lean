import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0818 : checkSingleBlackFast2 (23, -2) 11248 .south (-8, -1) (-20, -17) = true := by
  decide +kernel

end LangtonsAnt
