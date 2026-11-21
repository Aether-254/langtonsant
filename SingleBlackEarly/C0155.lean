import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0155 : checkSingleBlackFast (2, 7) 1799 .east (4, -7) (-10, -8) = true := by
  decide +kernel

end LangtonsAnt
