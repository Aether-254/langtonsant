import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0159 : checkSingleBlackFast (-1, 8) 3573 .east (0, -6) (-16, -11) = true := by
  decide +kernel

end LangtonsAnt
