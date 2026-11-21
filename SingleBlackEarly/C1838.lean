import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1838 : checkSingleBlackFast2 (-59, -33) 12412 .north (18, 10) (-44, -26) = true := by
  decide +kernel

end LangtonsAnt
