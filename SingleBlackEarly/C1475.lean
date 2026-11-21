import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1475 : checkSingleBlackFast (-26, -4) 36452 .north (4, 8) (-8, -38) = true := by
  decide +kernel

end LangtonsAnt
