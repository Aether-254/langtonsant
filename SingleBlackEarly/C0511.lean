import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0511 : checkSingleBlackFast (-6, -2) 3560 .north (0, -1) (-16, -9) = true := by
  decide +kernel

end LangtonsAnt
