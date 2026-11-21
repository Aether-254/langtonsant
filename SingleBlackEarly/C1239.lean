import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1239 : checkSingleBlackFast2 (12, 16) 17932 .north (-10, 6) (-8, -26) = true := by
  decide +kernel

end LangtonsAnt
