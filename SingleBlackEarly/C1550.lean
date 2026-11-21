import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1550 : checkSingleBlackFast (-30, -10) 23657 .east (8, -5) (-7, -35) = true := by
  decide +kernel

end LangtonsAnt
