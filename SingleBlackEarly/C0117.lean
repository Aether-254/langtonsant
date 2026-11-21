import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0117 : checkSingleBlackFast (6, 4) 3470 .north (0, 2) (-19, -5) = true := by
  decide +kernel

end LangtonsAnt
