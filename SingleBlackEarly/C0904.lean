import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0904 : checkSingleBlackFast2 (-11, 11) 16933 .east (1, -7) (-27, -14) = true := by
  decide +kernel

end LangtonsAnt
