import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1940 : checkSingleBlackFast2 (-67, -46) 15170 .north (27, 15) (-54, -26) = true := by
  decide +kernel

end LangtonsAnt
