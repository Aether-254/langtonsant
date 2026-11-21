import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0913 : checkSingleBlackFast2 (-11, 4) 15538 .south (-9, 3) (-26, -20) = true := by
  decide +kernel

end LangtonsAnt
