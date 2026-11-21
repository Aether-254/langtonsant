import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0884 : checkSingleBlackFast (-11, -1) 9603 .east (2, -7) (-22, -22) = true := by
  decide +kernel

end LangtonsAnt
