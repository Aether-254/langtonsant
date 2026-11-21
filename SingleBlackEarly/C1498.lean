import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1498 : checkSingleBlackFast (-29, -6) 35483 .east (7, -11) (-38, -3) = true := by
  decide +kernel

end LangtonsAnt
