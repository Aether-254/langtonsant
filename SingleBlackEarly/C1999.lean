import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1999 : checkSingleBlackFast2 (-74, -49) 18643 .east (25, 28) (3, -45) = true := by
  decide +kernel

end LangtonsAnt
