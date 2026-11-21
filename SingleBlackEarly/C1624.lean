import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1624 : checkSingleBlackFast (-39, -14) 19815 .east (22, -1) (-22, -40) = true := by
  decide +kernel

end LangtonsAnt
