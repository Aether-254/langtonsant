import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1842 : checkSingleBlackFast2 (-61, -34) 18834 .north (22, 15) (-49, -28) = true := by
  decide +kernel

end LangtonsAnt
