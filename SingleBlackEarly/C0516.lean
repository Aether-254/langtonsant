import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0516 : checkSingleBlackFast2 (-7, -6) 12885 .east (-4, -5) (-25, -15) = true := by
  decide +kernel

end LangtonsAnt
