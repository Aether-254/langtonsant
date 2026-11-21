import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0070 : checkSingleBlackFast (-3, -6) 1713 .west (0, 7) (-11, -5) = true := by
  decide +kernel

end LangtonsAnt
