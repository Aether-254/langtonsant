import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0197 : checkSingleBlackFast (11, 1) 1799 .east (0, -4) (-9, -8) = true := by
  decide +kernel

end LangtonsAnt
