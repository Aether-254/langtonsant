import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1003 : checkSingleBlackFast2 (-14, 10) 17776 .north (4, -3) (-28, -3) = true := by
  decide +kernel

end LangtonsAnt
