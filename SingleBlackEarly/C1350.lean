import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1350 : checkSingleBlackFast2 (-15, 7) 16851 .west (-8, 3) (-32, -6) = true := by
  decide +kernel

end LangtonsAnt
