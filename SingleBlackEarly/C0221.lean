import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0221 : checkSingleBlackFast2 (9, 9) 16896 .north (-5, -8) (-27, -12) = true := by
  decide +kernel

end LangtonsAnt
