import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1524 : checkSingleBlackFast (-30, -9) 22477 .east (3, -6) (-8, -32) = true := by
  decide +kernel

end LangtonsAnt
