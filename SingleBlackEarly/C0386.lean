import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0386 : checkSingleBlackFast (16, 3) 9410 .north (2, 7) (-7, -18) = true := by
  decide +kernel

end LangtonsAnt
