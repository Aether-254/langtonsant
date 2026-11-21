import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2070 : checkSingleBlackFast (-81, -58) 20685 .east (38, 23) (15, -57) = true := by
  decide +kernel

end LangtonsAnt
