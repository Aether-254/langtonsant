import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1551 : checkSingleBlackFast (-29, -11) 10968 .north (4, 0) (-30, -8) = true := by
  decide +kernel

end LangtonsAnt
