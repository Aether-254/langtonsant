import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0475 : checkSingleBlackFast2 (11, 13) 15044 .south (-11, -2) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
