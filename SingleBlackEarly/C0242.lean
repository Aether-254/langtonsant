import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0242 : checkSingleBlackFast2 (-5, -2) 12080 .north (-6, 6) (-4, -26) = true := by
  decide +kernel

end LangtonsAnt
