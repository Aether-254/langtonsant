import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1630 : checkSingleBlackFast2 (-41, -18) 18605 .east (18, 3) (-5, -37) = true := by
  decide +kernel

end LangtonsAnt
