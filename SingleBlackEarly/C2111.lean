import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2111 : checkSingleBlackFast2 (-84, -61) 15615 .west (29, 39) (-58, 19) = true := by
  decide +kernel

end LangtonsAnt
