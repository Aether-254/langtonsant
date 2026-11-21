import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1356 : checkSingleBlackFast2 (-15, 6) 10931 .east (-3, -7) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
