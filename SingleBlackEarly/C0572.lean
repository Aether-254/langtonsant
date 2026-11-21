import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0572 : checkSingleBlackFast2 (17, -2) 12811 .west (-1, -3) (-24, -11) = true := by
  decide +kernel

end LangtonsAnt
