import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0140 : checkSingleBlackFast (8, 0) 2355 .east (-2, -5) (-8, -10) = true := by
  decide +kernel

end LangtonsAnt
