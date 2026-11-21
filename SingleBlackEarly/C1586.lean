import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1586 : checkSingleBlackFast2 (-37, -14) 18397 .east (16, 1) (-7, -35) = true := by
  decide +kernel

end LangtonsAnt
