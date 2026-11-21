import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0535 : checkSingleBlackFast2 (2, -6) 15812 .south (-5, -3) (-29, -3) = true := by
  decide +kernel

end LangtonsAnt
