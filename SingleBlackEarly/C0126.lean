import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0126 : checkSingleBlackFast (5, 8) 2331 .west (-2, 2) (-11, -6) = true := by
  decide +kernel

end LangtonsAnt
