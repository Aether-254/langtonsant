import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0260 : checkSingleBlackFast (12, 11) 2427 .east (-4, -9) (-12, 2) = true := by
  decide +kernel

end LangtonsAnt
