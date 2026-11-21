import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2056 : checkSingleBlackFast2 (-76, -56) 16860 .north (33, 23) (-59, -39) = true := by
  decide +kernel

end LangtonsAnt
