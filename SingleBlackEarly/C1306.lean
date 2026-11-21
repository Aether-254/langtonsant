import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1306 : checkSingleBlackFast2 (-8, 19) 11071 .east (-6, -8) (-27, -10) = true := by
  decide +kernel

end LangtonsAnt
