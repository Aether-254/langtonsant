import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0355 : checkSingleBlackFast (-7, 4) 9318 .north (4, -8) (-25, -9) = true := by
  decide +kernel

end LangtonsAnt
