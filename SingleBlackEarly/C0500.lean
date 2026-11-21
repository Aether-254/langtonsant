import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0500 : checkSingleBlackFast2 (-1, 14) 11809 .west (-14, 7) (-23, -19) = true := by
  decide +kernel

end LangtonsAnt
