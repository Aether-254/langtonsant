import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0493 : checkSingleBlackFast2 (1, 14) 16829 .west (-9, 5) (-31, -16) = true := by
  decide +kernel

end LangtonsAnt
