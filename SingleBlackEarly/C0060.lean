import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0060 : checkSingleBlackFast (-4, -3) 4643 .east (-6, -5) (-8, -14) = true := by
  decide +kernel

end LangtonsAnt
