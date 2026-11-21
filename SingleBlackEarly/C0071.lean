import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0071 : checkSingleBlackFast (-2, -4) 996 .north (6, 5) (-8, -5) = true := by
  decide +kernel

end LangtonsAnt
