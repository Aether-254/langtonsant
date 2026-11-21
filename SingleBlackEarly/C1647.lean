import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1647 : checkSingleBlackFast2 (-42, -17) 16979 .east (9, 12) (-13, -29) = true := by
  decide +kernel

end LangtonsAnt
