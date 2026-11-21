import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0878 : checkSingleBlackFast2 (-11, 1) 11113 .east (-5, -6) (-24, -16) = true := by
  decide +kernel

end LangtonsAnt
