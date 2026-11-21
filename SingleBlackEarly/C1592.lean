import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1592 : checkSingleBlackFast (-34, -16) 26311 .east (7, -1) (-4, -35) = true := by
  decide +kernel

end LangtonsAnt
