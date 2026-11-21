import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1002 : checkSingleBlackFast2 (-14, 9) 11951 .east (-5, -8) (-27, -9) = true := by
  decide +kernel

end LangtonsAnt
