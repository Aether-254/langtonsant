import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2060 : checkSingleBlackFast2 (-80, -52) 18137 .west (33, 39) (-59, 16) = true := by
  decide +kernel

end LangtonsAnt
