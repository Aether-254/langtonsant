import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1436 : checkSingleBlackFast (-22, -1) 21185 .east (4, -3) (-21, -35) = true := by
  decide +kernel

end LangtonsAnt
