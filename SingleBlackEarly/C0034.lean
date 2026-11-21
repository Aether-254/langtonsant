import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0034 : checkSingleBlackFast (0, 2) 645 .east (3, -5) (-7, -2) = true := by
  decide +kernel

end LangtonsAnt
