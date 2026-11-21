import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0247 : checkSingleBlackFast (12, 4) 9509 .east (2, -7) (-17, -15) = true := by
  decide +kernel

end LangtonsAnt
