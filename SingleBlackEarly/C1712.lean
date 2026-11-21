import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1712 : checkSingleBlackFast (-47, -22) 20231 .east (26, 5) (-20, -44) = true := by
  decide +kernel

end LangtonsAnt
