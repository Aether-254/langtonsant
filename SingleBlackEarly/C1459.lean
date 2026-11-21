import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1459 : checkSingleBlackFast (-22, -3) 26823 .east (5, -14) (-33, -3) = true := by
  decide +kernel

end LangtonsAnt
