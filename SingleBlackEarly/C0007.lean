import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0007 : checkSingleBlackFast (-1, -1) 3111 .east (5, -5) (-14, -7) = true := by
  decide +kernel

end LangtonsAnt
