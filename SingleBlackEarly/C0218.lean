import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0218 : checkSingleBlackFast (11, 8) 2497 .east (-4, -9) (-13, -3) = true := by
  decide +kernel

end LangtonsAnt
