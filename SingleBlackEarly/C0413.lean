import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0413 : checkSingleBlackFast (17, -5) 3374 .south (-13, 0) (-18, 1) = true := by
  decide +kernel

end LangtonsAnt
