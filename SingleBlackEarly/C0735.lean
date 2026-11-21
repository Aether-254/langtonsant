import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0735 : checkSingleBlackFast (14, -12) 8946 .south (-8, -1) (-21, -10) = true := by
  decide +kernel

end LangtonsAnt
