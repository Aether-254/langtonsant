import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0038 : checkSingleBlackFast (-2, 4) 1747 .east (6, -7) (-10, -8) = true := by
  decide +kernel

end LangtonsAnt
