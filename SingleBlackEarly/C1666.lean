import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1666 : checkSingleBlackFast (-45, -18) 22249 .east (10, -6) (-38, -5) = true := by
  decide +kernel

end LangtonsAnt
