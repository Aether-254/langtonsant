import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0113 : checkSingleBlackFast (-4, -1) 5248 .south (-10, -4) (-20, -10) = true := by
  decide +kernel

end LangtonsAnt
