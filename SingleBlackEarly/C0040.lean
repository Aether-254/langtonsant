import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0040 : checkSingleBlackFast (-2, 2) 2459 .east (11, -4) (-13, -11) = true := by
  decide +kernel

end LangtonsAnt
