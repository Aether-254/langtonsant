import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0922 : checkSingleBlackFast2 (-11, 12) 16608 .north (-7, 2) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
