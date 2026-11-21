import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0419 : checkSingleBlackFast (15, 0) 11655 .east (-4, -3) (-18, -20) = true := by
  decide +kernel

end LangtonsAnt
