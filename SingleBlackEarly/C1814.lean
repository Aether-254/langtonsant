import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1814 : checkSingleBlackFast2 (-54, -34) 15716 .north (22, 12) (-48, -28) = true := by
  decide +kernel

end LangtonsAnt
