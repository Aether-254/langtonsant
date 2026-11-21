import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1460 : checkSingleBlackFast2 (-22, -4) 12315 .east (2, -2) (-21, -18) = true := by
  decide +kernel

end LangtonsAnt
