import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1310 : checkSingleBlackFast2 (-10, 17) 17156 .north (-3, 0) (3, -28) = true := by
  decide +kernel

end LangtonsAnt
