import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0476 : checkSingleBlackFast (10, 14) 7180 .south (-11, -8) (-19, -12) = true := by
  decide +kernel

end LangtonsAnt
