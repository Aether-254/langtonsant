import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1576 : checkSingleBlackFast2 (-36, -8) 15849 .west (11, 17) (-37, -6) = true := by
  decide +kernel

end LangtonsAnt
