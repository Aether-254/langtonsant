import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2137 : checkSingleBlackFast2 (-87, -63) 15823 .west (30, 41) (-60, 22) = true := by
  decide +kernel

end LangtonsAnt
