import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1920 : checkSingleBlackFast (-66, -45) 19925 .east (24, 14) (8, -47) = true := by
  decide +kernel

end LangtonsAnt
