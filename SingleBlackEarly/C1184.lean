import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1184 : checkSingleBlackFast2 (26, 1) 12140 .north (-3, 1) (-27, 3) = true := by
  decide +kernel

end LangtonsAnt
