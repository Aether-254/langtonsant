import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0912 : checkSingleBlackFast2 (-10, 4) 11625 .east (-4, -8) (-26, -5) = true := by
  decide +kernel

end LangtonsAnt
