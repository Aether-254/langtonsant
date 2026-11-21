import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0223 : checkSingleBlackFast (8, 9) 2062 .north (2, -2) (-11, -3) = true := by
  decide +kernel

end LangtonsAnt
