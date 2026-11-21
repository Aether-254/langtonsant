import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0148 : checkSingleBlackFast (3, 7) 2365 .east (0, -5) (-13, -5) = true := by
  decide +kernel

end LangtonsAnt
