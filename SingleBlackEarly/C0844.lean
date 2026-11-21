import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0844 : checkSingleBlackFast2 (-5, 10) 15802 .north (-2, -7) (-29, -12) = true := by
  decide +kernel

end LangtonsAnt
