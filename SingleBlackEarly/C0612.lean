import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0612 : checkSingleBlackFast (6, -6) 26021 .east (-11, -26) (-38, -4) = true := by
  decide +kernel

end LangtonsAnt
