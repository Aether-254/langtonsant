import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0956 : checkSingleBlackFast2 (8, 16) 11199 .east (-2, -3) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
