import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1946 : checkSingleBlackFast2 (-66, -46) 16340 .north (28, 18) (-54, -34) = true := by
  decide +kernel

end LangtonsAnt
