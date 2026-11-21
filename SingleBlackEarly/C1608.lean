import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1608 : checkSingleBlackFast2 (-39, -16) 18501 .east (17, 2) (-6, -36) = true := by
  decide +kernel

end LangtonsAnt
