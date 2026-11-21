import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0019 : checkSingleBlackFast (0, -2) 4441 .east (8, -2) (-10, -15) = true := by
  decide +kernel

end LangtonsAnt
