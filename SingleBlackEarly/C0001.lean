import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0001 : checkSingleBlackFast (1, 0) 3113 .east (4, -6) (-14, -7) = true := by
  decide +kernel

end LangtonsAnt
