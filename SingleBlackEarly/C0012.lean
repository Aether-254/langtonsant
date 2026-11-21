import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0012 : checkSingleBlackFast2 (-3, -1) 11780 .north (4, 2) (-24, -4) = true := by
  decide +kernel

end LangtonsAnt
