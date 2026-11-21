import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1673 : checkSingleBlackFast (-44, -22) 24483 .east (10, 3) (-18, -26) = true := by
  decide +kernel

end LangtonsAnt
