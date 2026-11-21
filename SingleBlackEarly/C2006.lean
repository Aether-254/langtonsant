import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2006 : checkSingleBlackFast2 (-73, -52) 15482 .north (30, 18) (-57, -29) = true := by
  decide +kernel

end LangtonsAnt
