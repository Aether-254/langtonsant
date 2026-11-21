import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0474 : checkSingleBlackFast2 (12, 15) 12912 .north (4, -4) (-24, 0) = true := by
  decide +kernel

end LangtonsAnt
