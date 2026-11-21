import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0494 : checkSingleBlackFast (1, 15) 8023 .east (-6, -6) (-21, -14) = true := by
  decide +kernel

end LangtonsAnt
