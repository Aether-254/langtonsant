import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0137 : checkSingleBlackFast (7, -1) 2263 .east (2, -7) (-10, -10) = true := by
  decide +kernel

end LangtonsAnt
