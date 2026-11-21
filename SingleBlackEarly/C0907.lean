import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0907 : checkSingleBlackFast2 (-12, 10) 15768 .south (-5, -6) (-17, -22) = true := by
  decide +kernel

end LangtonsAnt
