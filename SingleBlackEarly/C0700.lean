import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0700 : checkSingleBlackFast2 (21, -8) 11819 .east (-2, -4) (-17, -18) = true := by
  decide +kernel

end LangtonsAnt
