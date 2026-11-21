import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1222 : checkSingleBlackFast2 (11, 16) 12571 .east (-7, -1) (-20, -23) = true := by
  decide +kernel

end LangtonsAnt
