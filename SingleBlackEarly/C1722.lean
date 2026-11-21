import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1722 : checkSingleBlackFast2 (-48, -27) 18989 .east (15, 5) (-1, -38) = true := by
  decide +kernel

end LangtonsAnt
