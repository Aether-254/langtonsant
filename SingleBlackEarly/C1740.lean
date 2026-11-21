import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1740 : checkSingleBlackFast2 (-51, -28) 19125 .east (23, 8) (0, -42) = true := by
  decide +kernel

end LangtonsAnt
