import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1529 : checkSingleBlackFast (-27, -9) 10864 .north (3, 0) (-29, -6) = true := by
  decide +kernel

end LangtonsAnt
