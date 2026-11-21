import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1598 : checkSingleBlackFast2 (-38, -10) 15953 .west (12, 18) (-38, -5) = true := by
  decide +kernel

end LangtonsAnt
