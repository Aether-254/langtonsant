import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1503 : checkSingleBlackFast (-26, -7) 26208 .north (11, 5) (-45, -9) = true := by
  decide +kernel

end LangtonsAnt
