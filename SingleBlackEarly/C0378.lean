import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0378 : checkSingleBlackFast2 (15, -1) 10850 .north (-2, 7) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
