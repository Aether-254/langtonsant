import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2052 : checkSingleBlackFast (-78, -57) 20549 .east (30, 20) (14, -53) = true := by
  decide +kernel

end LangtonsAnt
