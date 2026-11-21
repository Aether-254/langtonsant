import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0029 : checkSingleBlackFast (1, 3) 8698 .north (12, 16) (-11, -19) = true := by
  decide +kernel

end LangtonsAnt
