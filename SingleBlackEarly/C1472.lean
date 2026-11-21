import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1472 : checkSingleBlackFast2 (-25, -3) 12027 .east (-1, -2) (-21, -21) = true := by
  decide +kernel

end LangtonsAnt
