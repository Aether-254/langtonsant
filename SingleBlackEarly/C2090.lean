import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2090 : checkSingleBlackFast2 (-82, -58) 15555 .west (28, 38) (-57, 18) = true := by
  decide +kernel

end LangtonsAnt
