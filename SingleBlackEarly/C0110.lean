import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0110 : checkSingleBlackFast (-4, 3) 1501 .east (4, -5) (-13, -7) = true := by
  decide +kernel

end LangtonsAnt
