import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2028 : checkSingleBlackFast2 (-75, -54) 15586 .north (31, 19) (-58, -30) = true := by
  decide +kernel

end LangtonsAnt
