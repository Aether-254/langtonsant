import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0580 : checkSingleBlackFast2 (21, -1) 29304 .north (3, -2) (-39, -8) = true := by
  decide +kernel

end LangtonsAnt
