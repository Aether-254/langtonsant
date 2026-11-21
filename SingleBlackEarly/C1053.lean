import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1053 : checkSingleBlackFast2 (-11, -6) 15023 .east (-5, -5) (-24, -17) = true := by
  decide +kernel

end LangtonsAnt
