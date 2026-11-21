import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0017 : checkSingleBlackFast (0, -4) 4615 .east (5, -6) (-17, -3) = true := by
  decide +kernel

end LangtonsAnt
