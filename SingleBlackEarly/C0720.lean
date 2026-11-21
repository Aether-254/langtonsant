import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0720 : checkSingleBlackFast2 (6, -12) 14136 .south (-10, 2) (-28, -16) = true := by
  decide +kernel

end LangtonsAnt
