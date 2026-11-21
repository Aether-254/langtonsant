import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0066 : checkSingleBlackFast (-3, -5) 9463 .east (8, 3) (-20, -10) = true := by
  decide +kernel

end LangtonsAnt
