import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0375 : checkSingleBlackFast2 (14, -2) 19016 .south (-10, -3) (-28, -21) = true := by
  decide +kernel

end LangtonsAnt
