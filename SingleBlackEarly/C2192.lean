import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2192 : checkSingleBlackFast2 (-92, -64) 18761 .west (39, 45) (-65, 22) = true := by
  decide +kernel

end LangtonsAnt
