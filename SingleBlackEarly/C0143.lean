import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0143 : checkSingleBlackFast (7, 2) 1815 .east (2, -3) (-10, -6) = true := by
  decide +kernel

end LangtonsAnt
