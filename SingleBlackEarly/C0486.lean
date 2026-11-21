import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0486 : checkSingleBlackFast2 (6, 14) 11656 .north (-5, 8) (1, -20) = true := by
  decide +kernel

end LangtonsAnt
