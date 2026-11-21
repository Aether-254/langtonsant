import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0394 : checkSingleBlackFast (10, -5) 4452 .south (-12, 2) (-18, -2) = true := by
  decide +kernel

end LangtonsAnt
