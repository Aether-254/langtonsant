import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0078 : checkSingleBlackFast (4, -4) 8681 .east (-3, -8) (-20, -14) = true := by
  decide +kernel

end LangtonsAnt
