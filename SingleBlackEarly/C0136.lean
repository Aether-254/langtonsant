import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0136 : checkSingleBlackFast2 (7, 0) 11016 .north (2, 6) (-22, -18) = true := by
  decide +kernel

end LangtonsAnt
