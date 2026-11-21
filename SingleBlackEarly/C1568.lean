import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1568 : checkSingleBlackFast2 (-34, -13) 17381 .east (10, -7) (-7, -33) = true := by
  decide +kernel

end LangtonsAnt
