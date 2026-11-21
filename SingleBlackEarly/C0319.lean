import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0319 : checkSingleBlackFast (0, 10) 7083 .east (-8, -1) (-14, -18) = true := by
  decide +kernel

end LangtonsAnt
