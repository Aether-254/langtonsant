import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2021 : checkSingleBlackFast2 (-76, -51) 18747 .east (26, 29) (4, -46) = true := by
  decide +kernel

end LangtonsAnt
