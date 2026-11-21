import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0520 : checkSingleBlackFast (-6, -7) 5674 .north (4, -2) (-21, -9) = true := by
  decide +kernel

end LangtonsAnt
