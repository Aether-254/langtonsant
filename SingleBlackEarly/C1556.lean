import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1556 : checkSingleBlackFast (-35, -8) 19419 .east (2, -6) (-7, -32) = true := by
  decide +kernel

end LangtonsAnt
