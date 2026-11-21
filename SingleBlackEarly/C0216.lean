import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0216 : checkSingleBlackFast (10, 6) 28111 .east (-7, -9) (-36, 1) = true := by
  decide +kernel

end LangtonsAnt
