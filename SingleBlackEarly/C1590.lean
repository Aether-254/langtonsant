import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1590 : checkSingleBlackFast2 (-36, -15) 29505 .east (9, -8) (-6, -38) = true := by
  decide +kernel

end LangtonsAnt
