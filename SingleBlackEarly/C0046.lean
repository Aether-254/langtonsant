import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0046 : checkSingleBlackFast (-2, 1) 817 .east (6, -4) (-8, -3) = true := by
  decide +kernel

end LangtonsAnt
