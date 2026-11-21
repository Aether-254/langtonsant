import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0061 : checkSingleBlackFast (-4, -2) 2687 .east (6, -7) (-10, -12) = true := by
  decide +kernel

end LangtonsAnt
