import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0644 : checkSingleBlackFast2 (5, -10) 10820 .north (0, -2) (-24, 0) = true := by
  decide +kernel

end LangtonsAnt
