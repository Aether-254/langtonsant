import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0146 : checkSingleBlackFast (8, 2) 2225 .east (-2, -7) (-13, -5) = true := by
  decide +kernel

end LangtonsAnt
