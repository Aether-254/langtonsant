import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0142 : checkSingleBlackFast (6, 2) 1847 .east (1, -3) (-10, -7) = true := by
  decide +kernel

end LangtonsAnt
