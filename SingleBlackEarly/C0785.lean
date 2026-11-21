import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0785 : checkSingleBlackFast (25, -10) 10502 .south (-8, 4) (-21, -15) = true := by
  decide +kernel

end LangtonsAnt
