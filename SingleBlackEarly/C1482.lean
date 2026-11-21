import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1482 : checkSingleBlackFast (-24, -6) 19432 .north (11, -8) (-37, -2) = true := by
  decide +kernel

end LangtonsAnt
