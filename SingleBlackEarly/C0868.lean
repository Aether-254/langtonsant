import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0868 : checkSingleBlackFast (-8, 1) 10107 .east (2, -5) (-20, -22) = true := by
  decide +kernel

end LangtonsAnt
