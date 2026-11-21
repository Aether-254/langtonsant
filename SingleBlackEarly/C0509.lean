import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0509 : checkSingleBlackFast2 (-5, 0) 16261 .east (-3, -8) (-28, 0) = true := by
  decide +kernel

end LangtonsAnt
