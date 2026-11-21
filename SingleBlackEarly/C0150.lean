import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0150 : checkSingleBlackFast (0, 5) 4068 .south (-5, -8) (-13, -14) = true := by
  decide +kernel

end LangtonsAnt
