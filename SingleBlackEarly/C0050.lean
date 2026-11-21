import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0050 : checkSingleBlackFast (1, -4) 6136 .north (5, 6) (-15, -16) = true := by
  decide +kernel

end LangtonsAnt
