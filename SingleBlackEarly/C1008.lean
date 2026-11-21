import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1008 : checkSingleBlackFast2 (-13, 7) 16839 .west (-8, 3) (-32, -6) = true := by
  decide +kernel

end LangtonsAnt
