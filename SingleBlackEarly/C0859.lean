import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0859 : checkSingleBlackFast (-8, 7) 7001 .east (0, -4) (-18, -19) = true := by
  decide +kernel

end LangtonsAnt
