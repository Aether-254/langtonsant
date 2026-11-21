import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2128 : checkSingleBlackFast (-87, -60) 20186 .north (35, 28) (-62, -41) = true := by
  decide +kernel

end LangtonsAnt
