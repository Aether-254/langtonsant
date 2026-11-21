import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0499 : checkSingleBlackFast (0, 14) 22146 .south (-18, -2) (-33, 3) = true := by
  decide +kernel

end LangtonsAnt
