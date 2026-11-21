import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0239 : checkSingleBlackFast (3, 10) 2046 .north (2, -3) (-11, -4) = true := by
  decide +kernel

end LangtonsAnt
