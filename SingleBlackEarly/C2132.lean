import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2132 : checkSingleBlackFast2 (-85, -63) 17145 .west (30, 39) (-59, 19) = true := by
  decide +kernel

end LangtonsAnt
