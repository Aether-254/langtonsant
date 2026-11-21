import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1822 : checkSingleBlackFast (-57, -32) 20751 .east (31, 10) (-15, -49) = true := by
  decide +kernel

end LangtonsAnt
