import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1799 : checkSingleBlackFast (-57, -29) 25313 .east (24, 12) (2, -47) = true := by
  decide +kernel

end LangtonsAnt
