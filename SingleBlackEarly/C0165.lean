import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0165 : checkSingleBlackFast (-2, 6) 6853 .east (0, -8) (-18, -7) = true := by
  decide +kernel

end LangtonsAnt
