import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0891 : checkSingleBlackFast2 (-8, -2) 16127 .west (-15, -2) (-23, -27) = true := by
  decide +kernel

end LangtonsAnt
