import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1876 : checkSingleBlackFast (-62, -41) 19717 .east (22, 12) (6, -45) = true := by
  decide +kernel

end LangtonsAnt
