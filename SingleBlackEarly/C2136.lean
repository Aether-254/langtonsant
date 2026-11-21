import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2136 : checkSingleBlackFast (-87, -64) 20997 .east (41, 26) (18, -60) = true := by
  decide +kernel

end LangtonsAnt
