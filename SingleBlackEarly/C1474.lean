import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1474 : checkSingleBlackFast (-26, -2) 20041 .east (5, -7) (-11, -34) = true := by
  decide +kernel

end LangtonsAnt
